/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGramSchmidt.Basic
public import HexBareiss.Bareiss
public import HexDeterminant

public section

/-!
Executable array/loop machinery for the integer scaled Gram-Schmidt pass in
`hex-gram-schmidt`.

This module defines the integer-determinant surface (`gramDet` and
`independent`, the leading Gram matrices (`leadingGramMatrixInt`/`Rat`),
`scaledCoeffMatrix`, lattice membership `memLattice`, and the no-pivot Bareiss
determinant reader `gramDetVecEntry`) together with the mutable row-major array
kernel that computes the scaled coefficients fraction-free. The kernel includes the
nested-array storage (`gramRows`, `zeroRows`, `getArrayEntry`/`setArrayEntry`,
`rowsToMatrix`), the Bareiss-style elimination sweep `stepScaledRows` and
column-writer `writeScaledColumn`, the driver `scaledCoeffArrayLoop`, the two
formulations `scaledCoeffRows` (reference) and `scaledCoeffRowsSchur` (live
per-row Schur recurrence, with `schurSigma`/`schurScaledCoeffEntry`), and a
large body of frame/size bookkeeping lemmas plus the per-step correspondence
`rowsToMatrix_stepScaledRows_eq` between the array update and `Matrix.stepMatrix`.
-/
namespace Hex

namespace GramSchmidt

/-- Promote an index into a shorter prefix to the ambient matrix height. -/
@[expose]
def liftFinLE (i : Fin k) (hk : k ≤ n) : Fin n :=
  ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩

/-- Leading principal Gram matrix of the first `k` rows of an integer basis. -/
@[expose]
def leadingGramMatrixInt (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) : Matrix Int k k :=
  Matrix.ofFn fun i j =>
    (b.row (liftFinLE i hk)).dotProduct (b.row (liftFinLE j hk))

/-- The Gram-Schmidt leading Gram matrix is the leading prefix of the full
Gram matrix. This is the shape equation between the public `gramDet` API and
the one-pass `gramDetVec` implementation. -/
theorem leadingGramMatrixInt_eq_principalSubmatrix_gram
    (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) :
    leadingGramMatrixInt b k hk =
      Matrix.principalSubmatrix (Matrix.gramMatrix b) k hk := by
  apply Hex.Matrix.ext
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [leadingGramMatrixInt, Matrix.principalSubmatrix, Matrix.gramMatrix, Vector.dotProduct, Matrix.ofFn,
    liftFinLE]

/-- Leading principal Gram matrix of the first `k` rows of a rational basis. -/
@[expose]
def leadingGramMatrixRat (b : Matrix Rat n m) (k : Nat) (hk : k ≤ n) : Matrix Rat k k :=
  Matrix.ofFn fun i j =>
    (b.row (liftFinLE i hk)).dotProduct (b.row (liftFinLE j hk))

/-- Determinant matrix used by the integral `scaledCoeffs` entry formula:
take the leading `j + 1` Gram matrix and replace its last column by the inner
products with row `i`. -/
@[expose]
def scaledCoeffMatrix (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) :
    Matrix Int (j.val + 1) (j.val + 1) :=
  let hk : j.val + 1 ≤ n := Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt)
  Matrix.ofFn fun p q =>
    let p' := liftFinLE p hk
    if q.val = j.val then
      (b.row p').dotProduct (b.row i)
    else
      let q' := liftFinLE q hk
      (b.row p').dotProduct (b.row q')

end GramSchmidt

namespace GramSchmidt.Int

/-- Integer lattice membership in the row span of `b`. This mirrors the LLL
predicate without making `hex-gram-schmidt` depend on the downstream LLL
library. -/
@[expose]
def memLattice (b : Matrix Int n m) (v : Vector Int m) : Prop :=
  ∃ c : Vector Int n, Matrix.vecMul c b = v

/-- The `k`-th Gram determinant: the determinant of the `k × k` leading
principal Gram matrix of the integer input. -/
@[expose]
def gramDet (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) : Nat :=
  (Matrix.bareiss (GramSchmidt.leadingGramMatrixInt b k hk)).toNat

/-- Linear independence of the row prefix determinants used by the
Gram-Schmidt theorem surface, stated over the Mathlib-free executable
`gramDet` data. -/
@[expose]
def independent (b : Matrix Int n m) : Prop :=
  ∀ k : Fin n, 0 < gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt)

/-- Product of the squared Gram-Schmidt basis norms along the first `k` rows. -/
@[expose]
noncomputable def gramSchmidtNormProduct (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) :
    Rat :=
  (List.finRange k).foldl
    (fun acc j =>
      let jn : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
      acc * ((basis b).row jn).normSq)
    1

/-- Read a diagonal entry from a Bareiss elimination matrix as a natural
determinant value. -/
@[expose]
def bareissDiagNat (data : Matrix.BareissData n) (r : Nat) (hr : r < n) : Nat :=
  let i : Fin n := ⟨r, hr⟩
  (data.matrix[(i, i)]).toNat

/-- Read the `k`-th leading-principal determinant from one no-pivot Bareiss
elimination pass over the full Gram matrix. This helper is only used for Gram
matrices: once a leading row prefix is singular, every larger leading prefix is
also singular, so all later leading determinants are zero. -/
@[expose]
def gramDetVecEntry (data : Matrix.BareissData n) (k : Fin (n + 1)) : Nat :=
  match hk : k.val with
  | 0 => 1
  | r + 1 =>
      have hrSucc : r + 1 < n + 1 := by
        simpa [hk] using k.isLt
      have hr : r < n := Nat.succ_lt_succ_iff.mp hrSucc
      match data.singularStep with
      | some s => if s < r + 1 then 0 else
          bareissDiagNat data r hr
      | none => bareissDiagNat data r hr

/-- After a no-pivot Bareiss pass records a singular step, every later
`gramDetVecEntry` slot is the encoded zero tail rather than a diagonal read. -/
private theorem gramDetVecEntry_eq_zero_of_singularStep_lt
    (data : Matrix.BareissData n) (s r : Nat) (hr : r < n)
    (hsing : data.singularStep = some s) (hs : s < r + 1) :
    gramDetVecEntry data ⟨r + 1, Nat.succ_lt_succ hr⟩ = 0 := by
  simp [gramDetVecEntry, hsing, hs]

/-- Specialization of the encoded zero-tail fact to the no-pivot executable
data used by the Gram determinant vector pass. -/
theorem gramDetVecEntry_noPivot_eq_zero_of_singularStep_lt
    (b : Matrix Int n m) (s r : Nat) (hr : r < n)
    (hsing : (Matrix.bareissNoPivotData (Matrix.gramMatrix b)).singularStep = some s)
    (hs : s < r + 1) :
    gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
        ⟨r + 1, Nat.succ_lt_succ hr⟩ = 0 :=
  gramDetVecEntry_eq_zero_of_singularStep_lt
    (Matrix.bareissNoPivotData (Matrix.gramMatrix b)) s r hr hsing hs

/-- Mutable loop state for the integer scaled Gram-Schmidt pass: the current
step, the working matrix and coefficient arrays, and the previous Bareiss
pivot. -/
structure ScaledCoeffArrayState where
  step : Nat
  matrix : Array (Array Int)
  coeffs : Array (Array Int)
  prevPivot : Int

/-- Read entry `(row, col)` from a row-major nested array as `rows[row]![col]!`. -/
@[inline] def getArrayEntry (rows : Array (Array Int)) (row col : Nat) : Int :=
  rows[row]![col]!

/-- An `n × n` row-major nested array initialised to all zeros. -/
@[expose]
def zeroRows (n : Nat) : Array (Array Int) :=
  Array.replicate n (Array.replicate n 0)

/-- The Gram matrix of `b` packaged as a row-major nested integer array. -/
@[expose]
def gramRows (b : Matrix Int n m) : Array (Array Int) :=
  Array.ofFn fun i : Fin n =>
    Array.ofFn fun j : Fin n =>
      (b.row i).dotProduct (b.row j)

/-- Reading entry `(i, j)` of `gramRows b` recovers the Gram matrix entry
`(gramMatrix b)[i][j]`. -/
private theorem getArrayEntry_gramRows (b : Matrix Int n m) (i j : Fin n) :
    getArrayEntry (gramRows b) i.val j.val = (Matrix.gramMatrix b)[i][j] := by
  simp [getArrayEntry, gramRows, Matrix.gramMatrix, Vector.dotProduct, Matrix.ofFn]

/-- Reconstruct an `n × n` integer matrix from a row-major nested array, reading
entry `(i, j)` as `rows[i]![j]!` (`getArrayEntry`). This converts the executable
array passes back to the `Matrix` API; for the Gram rows it inverts `gramRows`,
so `rowsToMatrix (gramRows b) n = gramMatrix b`. -/
@[expose]
def rowsToMatrix (rows : Array (Array Int)) (n : Nat) : Matrix Int n n :=
  Matrix.ofFn fun i j => getArrayEntry rows i.val j.val

/-- `rowsToMatrix` inverts `gramRows`, recovering `gramMatrix b` from its
nested-array packaging. -/
private theorem rowsToMatrix_gramRows (b : Matrix Int n m) :
    rowsToMatrix (gramRows b) n = Matrix.gramMatrix b := by
  apply Hex.Matrix.ext
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simpa [rowsToMatrix, Matrix.ofFn, Hex.Matrix.getRow, Fin.getElem_fin] using
    getArrayEntry_gramRows b (⟨i, hi⟩ : Fin n) (⟨j, hj⟩ : Fin n)

/-- Write `value` into entry `(row, col)` of a row-major nested array. -/
@[expose]
def setArrayEntry (rows : Array (Array Int)) (row col : Nat) (value : Int) :
    Array (Array Int) :=
  rows.set! row (rows[row]!.set! col value)

/-- Reading back the just-written index of `Array.set!` returns the written
value, when the index is in bounds. -/
private theorem array_getElem!_set!_same {α : Type} [Inhabited α]
    (xs : Array α) {i : Nat} (hi : i < xs.size) (v : α) :
    (xs.set! i v)[i]! = v := by
  rw [Array.getElem!_eq_getD]
  simp [Array.getD, Array.set!_eq_setIfInBounds, hi]

/-- Reading a different index after `Array.set!` returns the original element. -/
private theorem array_getElem!_set!_ne {α : Type} [Inhabited α]
    (xs : Array α) {i j : Nat} (hij : j ≠ i) (v : α) :
    (xs.set! i v)[j]! = xs[j]! := by
  rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD]
  unfold Array.set!
  unfold Array.setIfInBounds
  by_cases hi : i < xs.size
  · simp [hi]
    rw [Array.getElem?_set]
    simp [hij.symm]
  · simp [hi]

/-- `setArrayEntry` leaves entries in any other row unchanged. -/
private theorem getArrayEntry_setArrayEntry_of_row_ne
    (rows : Array (Array Int)) (row col r c : Nat) (value : Int) (hr : r ≠ row) :
    getArrayEntry (setArrayEntry rows row col value) r c = getArrayEntry rows r c := by
  grind [getArrayEntry, setArrayEntry]

/-- `setArrayEntry` leaves entries in any other column of the written row
unchanged. -/
private theorem getArrayEntry_setArrayEntry_of_col_ne
    (rows : Array (Array Int)) (row col c : Nat) (value : Int) (hc : c ≠ col) :
    getArrayEntry (setArrayEntry rows row col value) row c = getArrayEntry rows row c := by
  grind [getArrayEntry, setArrayEntry]

/-- Reading back the just-written entry of `setArrayEntry` returns the written
value, when both indices are in bounds. -/
private theorem getArrayEntry_setArrayEntry_self
    (rows : Array (Array Int)) (row col : Nat) (value : Int)
    (hrow : row < rows.size) (hcol : col < rows[row]!.size) :
    getArrayEntry (setArrayEntry rows row col value) row col = value := by
  unfold getArrayEntry setArrayEntry
  rw [array_getElem!_set!_same rows hrow (rows[row]!.set! col value)]
  exact array_getElem!_set!_same rows[row]! hcol value

/-- `setArrayEntry` preserves the outer-array size. -/
private theorem setArrayEntry_size (rows : Array (Array Int)) (row col : Nat) (value : Int) :
    (setArrayEntry rows row col value).size = rows.size := by
  simp [setArrayEntry, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

/-- `setArrayEntry` preserves each inner row's size. -/
private theorem setArrayEntry_rows_size
    (rows : Array (Array Int)) (row col r : Nat) (value : Int) :
    (setArrayEntry rows row col value)[r]!.size = rows[r]!.size := by
  unfold setArrayEntry
  by_cases hrow : r = row
  · subst r
    by_cases hbound : row < rows.size
    · rw [array_getElem!_set!_same _ hbound]
      simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
    · simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, hbound]
  · simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.set!_eq_setIfInBounds]
    have hne : row ≠ r := fun h => hrow h.symm
    by_cases hbound : row < rows.size
    · simp [hne]
    · simp [Array.setIfInBounds, hbound]

/-- A `foldl` of column-`k` writes over rows all exceeding `k` leaves entries
strictly above the diagonal (`i < j`) unchanged. -/
private theorem getArrayEntry_foldl_setArrayEntry_col_above
    (xs : List Nat) (coeffs rows : Array (Array Int)) (k i j : Nat)
    (hxs : ∀ x ∈ xs, k < x) (hij : i < j) :
    getArrayEntry
        (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) coeffs)
        i j =
      getArrayEntry coeffs i j := by
  induction xs generalizing coeffs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : k < x := hxs x (by simp)
      have hxs' : ∀ y ∈ xs, k < y := by
        intro y hy
        exact hxs y (by simp [hy])
      simp only [List.foldl_cons]
      rw [ih (setArrayEntry coeffs x k (getArrayEntry rows x k)) hxs']
      by_cases hrow : i = x
      · subst x
        rw [getArrayEntry_setArrayEntry_of_col_ne]
        omega
      · rw [getArrayEntry_setArrayEntry_of_row_ne]
        exact hrow

/-- A `foldl` of column-`k` writes over rows all exceeding `k` leaves entries
in rows at or below `k` unchanged. -/
private theorem getArrayEntry_foldl_setArrayEntry_row_ne
    (xs : List Nat) (coeffs rows : Array (Array Int)) (k i j : Nat)
    (hxs : ∀ x ∈ xs, k < x) (hi : i ≤ k) :
    getArrayEntry
        (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) coeffs)
        i j =
      getArrayEntry coeffs i j := by
  induction xs generalizing coeffs with
  | nil =>
      simp
  | cons x xs ih =>
      have hx : k < x := hxs x (by simp)
      have hxs' : ∀ y ∈ xs, k < y := by
        intro y hy
        exact hxs y (by simp [hy])
      simp only [List.foldl_cons]
      rw [ih (setArrayEntry coeffs x k (getArrayEntry rows x k)) hxs',
        getArrayEntry_setArrayEntry_of_row_ne]
      omega

/-- A column-targeted `foldl` preserves rows whose index is absent from the
write list. -/
private theorem getArrayEntry_foldl_setArrayEntry_row_notMem
    (xs : List Nat) (coeffs rows : Array (Array Int)) (k r c : Nat)
    (hr : r ∉ xs) :
    getArrayEntry
        (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) coeffs)
        r c =
      getArrayEntry coeffs r c := by
  induction xs generalizing coeffs with
  | nil =>
      simp
  | cons x xs ih =>
      have hrx : r ≠ x := fun h => hr (h ▸ List.mem_cons_self)
      have hrxs : r ∉ xs := fun h => hr (List.mem_cons_of_mem _ h)
      simp only [List.foldl_cons]
      rw [ih (setArrayEntry coeffs x k (getArrayEntry rows x k)) hrxs,
        getArrayEntry_setArrayEntry_of_row_ne]
      exact hrx

/-- A column-targeted `foldl` of `setArrayEntry`s at column `k` leaves entries
in any other column unchanged. -/
private theorem getArrayEntry_foldl_setArrayEntry_col_ne
    (xs : List Nat) (coeffs rows : Array (Array Int)) (k r c : Nat) (hc : c ≠ k) :
    getArrayEntry
        (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) coeffs)
        r c =
      getArrayEntry coeffs r c := by
  induction xs generalizing coeffs with
  | nil =>
      simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (setArrayEntry coeffs x k (getArrayEntry rows x k))]
      by_cases hrow : r = x
      · subst x
        rw [getArrayEntry_setArrayEntry_of_col_ne _ _ _ _ _ hc]
      · rw [getArrayEntry_setArrayEntry_of_row_ne]
        exact hrow

/-- A column-targeted `foldl` records the source-row value at an updated row.
The row list is nodup, so the final write to `r` is the unique write to that
row. -/
private theorem getArrayEntry_foldl_setArrayEntry_col_mem
    (xs : List Nat) (coeffs rows : Array (Array Int)) (k r : Nat)
    (hrmem : r ∈ xs) (hnodup : xs.Nodup)
    (hrow : r < coeffs.size) (hcol : k < coeffs[r]!.size) :
    getArrayEntry
        (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) coeffs)
        r k =
      getArrayEntry rows r k := by
  induction xs generalizing coeffs with
  | nil =>
      exact absurd hrmem (by simp)
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hnodup' : xs.Nodup := hnodup.tail
      have hxnotmem : x ∉ xs := by
        simp [List.nodup_cons] at hnodup
        exact hnodup.1
      rcases List.mem_cons.mp hrmem with hr_eq | hr_in
      · subst x
        rw [getArrayEntry_foldl_setArrayEntry_row_notMem]
        · exact getArrayEntry_setArrayEntry_self coeffs r k
            (getArrayEntry rows r k) hrow hcol
        · exact hxnotmem
      · have hr_ne_x : r ≠ x := by
          intro h
          subst r
          exact hxnotmem hr_in
        have hrow' : r < (setArrayEntry coeffs x k (getArrayEntry rows x k)).size := by
          simp [setArrayEntry, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hrow]
        have hcol' :
            k < (setArrayEntry coeffs x k (getArrayEntry rows x k))[r]!.size := by
          unfold setArrayEntry
          rw [array_getElem!_set!_ne _ hr_ne_x]
          exact hcol
        exact ih (setArrayEntry coeffs x k (getArrayEntry rows x k))
          hr_in hnodup' hrow' hcol'

/-- A `foldl` whose write value reads the same column being written still
leaves non-member indices unchanged. -/
private theorem getElem!_foldl_setSelf_of_notMem
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α → α) (r : Nat)
    (hr : r ∉ xs) :
    (xs.foldl (fun next x => next.set! x (f x next[x]!)) arr)[r]! = arr[r]! := by
  induction xs generalizing arr with
  | nil => simp
  | cons x xs ih =>
      have hx : r ≠ x := fun h => hr (h ▸ List.mem_cons_self)
      have hxs : r ∉ xs := fun h => hr (List.mem_cons_of_mem _ h)
      simp only [List.foldl_cons]
      rw [ih _ hxs]
      grind

/-- A `foldl` whose write value reads the same column being written writes the
function of the original value at every member index of a `Nodup` list. -/
private theorem getElem!_foldl_setSelf_of_mem_nodup
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α → α) (r : Nat)
    (hr : r ∈ xs) (hnodup : xs.Nodup) (hbound : r < arr.size) :
    (xs.foldl (fun next x => next.set! x (f x next[x]!)) arr)[r]! = f r arr[r]! := by
  induction xs generalizing arr with
  | nil => exact absurd hr (by simp)
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hnodup' : xs.Nodup := hnodup.tail
      have hxnotmem : x ∉ xs := by
        simp [List.nodup_cons] at hnodup
        exact hnodup.1
      rcases List.mem_cons.mp hr with hr_eq | hr_in
      · subst hr_eq
        rw [getElem!_foldl_setSelf_of_notMem _ _ _ _ hxnotmem]
        grind
      · have hr_ne_x : r ≠ x := by
          intro h
          exact hxnotmem (h ▸ hr_in)
        have hbound' : r < (arr.set! x (f x arr[x]!)).size := by
          simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hbound]
        rw [ih _ hr_in hnodup' hbound']
        grind

/-- A `foldl` that sets indices via values read from the row itself preserves
the array size. -/
private theorem size_foldl_setSelf
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α → α) :
    (xs.foldl (fun next x => next.set! x (f x next[x]!)) arr).size = arr.size := by
  induction xs generalizing arr with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

/-- `Array.modify` equals `Array.set!` applied to the function's value at the
current entry. -/
private theorem modify_eq_set!
    {α : Type} [Inhabited α] (arr : Array α) (i : Nat) (f : α → α) :
    arr.modify i f = arr.set! i (f arr[i]!) := by
  -- `Array.modify`/`modifyM` are public but not `@[expose]`d, so prove via the
  -- exposed `@[grind]` lemma API rather than unfolding the definitions.
  grind

/-- `Array.modify` leaves any index other than the modified one unchanged. -/
private theorem getElem!_modify_ne
    {α : Type} [Inhabited α] (arr : Array α) (i r : Nat) (f : α → α)
    (hr : r ≠ i) :
    (arr.modify i f)[r]! = arr[r]! := by
  rw [modify_eq_set!]
  grind

/-- Reading back the modified index of `Array.modify` returns `f` applied to the
original entry, when the index is in bounds. -/
private theorem getElem!_modify_self
    {α : Type} [Inhabited α] (arr : Array α) (i : Nat) (f : α → α)
    (hi : i < arr.size) :
    (arr.modify i f)[i]! = f arr[i]! := by
  rw [modify_eq_set!]
  grind

/-- `Array.modify` preserves the array size. -/
private theorem modify_size
    {α : Type} [Inhabited α] (arr : Array α) (i : Nat) (f : α → α) :
    (arr.modify i f).size = arr.size := by
  rw [modify_eq_set!]
  simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

/-- A `foldl` that modifies indices appearing in `xs` leaves untouched
indices unchanged. -/
private theorem getElem!_foldl_modify_of_notMem
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α → α) (r : Nat)
    (hr : r ∉ xs) :
    (xs.foldl (fun next x => next.modify x (f x)) arr)[r]! = arr[r]! := by
  induction xs generalizing arr with
  | nil => simp
  | cons x xs ih =>
      have hx : r ≠ x := fun h => hr (h ▸ List.mem_cons_self)
      have hxs : r ∉ xs := fun h => hr (List.mem_cons_of_mem _ h)
      simp only [List.foldl_cons]
      rw [ih _ hxs]
      exact getElem!_modify_ne arr x r (f x) hx

/-- A `foldl` that modifies indices appearing in a `Nodup` list `xs` writes
the modified original value at every member index `r` that is in-bounds for the
input array. -/
private theorem getElem!_foldl_modify_of_mem_nodup
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α → α) (r : Nat)
    (hr : r ∈ xs) (hnodup : xs.Nodup) (hbound : r < arr.size) :
    (xs.foldl (fun next x => next.modify x (f x)) arr)[r]! = f r arr[r]! := by
  induction xs generalizing arr with
  | nil => exact absurd hr (by simp)
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hnodup' : xs.Nodup := hnodup.tail
      have hxnotmem : x ∉ xs := by
        simp [List.nodup_cons] at hnodup
        exact hnodup.1
      rcases List.mem_cons.mp hr with hr_eq | hr_in
      · subst hr_eq
        rw [getElem!_foldl_modify_of_notMem _ _ _ _ hxnotmem]
        exact getElem!_modify_self arr r (f r) hbound
      · have hr_ne_x : r ≠ x := by
          intro h
          exact hxnotmem (h ▸ hr_in)
        have hbound' : r < (arr.modify x (f x)).size := by
          rw [modify_size]
          exact hbound
        rw [ih _ hr_in hnodup' hbound', getElem!_modify_ne arr x r (f x) hr_ne_x]

/-- A `foldl` that modifies indices via `Array.modify` preserves the outer
array size. -/
private theorem size_foldl_modify
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α → α) :
    (xs.foldl (fun next x => next.modify x (f x)) arr).size = arr.size := by
  induction xs generalizing arr with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact modify_size arr x (f x)

/-- Write column `k` of the coefficient array, copying the matrix-column values
from row `k` downward. -/
@[expose]
def writeScaledColumn (coeffs rows : Array (Array Int)) (n k : Nat) :
    Array (Array Int) :=
  Id.run do
    let mut next := setArrayEntry coeffs k k (getArrayEntry rows k k)
    for i in [k + 1:n] do
      next := setArrayEntry next i k (getArrayEntry rows i k)
    return next

/-- `writeScaledColumn` leaves strictly-above-diagonal entries (`i < j`)
unchanged. -/
private theorem getArrayEntry_writeScaledColumn_above
    (coeffs rows : Array (Array Int)) (n k i j : Nat) (hij : i < j) :
    getArrayEntry (writeScaledColumn coeffs rows n k) i j = getArrayEntry coeffs i j := by
  unfold writeScaledColumn
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [getArrayEntry_foldl_setArrayEntry_col_above]
  · by_cases hrow : i = k
    · subst k
      rw [getArrayEntry_setArrayEntry_of_col_ne]
      omega
    · rw [getArrayEntry_setArrayEntry_of_row_ne]
      exact hrow
  · intro x hx
    simp at hx
    omega
  · exact hij

/-- `writeScaledColumn` writes the matrix diagonal entry `(k, k)` into the
coefficient diagonal. -/
private theorem getArrayEntry_writeScaledColumn_diag
    (coeffs rows : Array (Array Int)) (n k : Nat)
    (hrow : k < coeffs.size) (hcol : k < coeffs[k]!.size) :
    getArrayEntry (writeScaledColumn coeffs rows n k) k k =
      getArrayEntry rows k k := by
  unfold writeScaledColumn
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [getArrayEntry_foldl_setArrayEntry_row_ne]
  · rw [getArrayEntry_setArrayEntry_self _ _ _ _ hrow hcol]
  · intro x hx
    simp at hx
    omega
  · omega

/-- Below the current pivot row, `writeScaledColumn` records the current
matrix-column value in the coefficient column. -/
private theorem getArrayEntry_writeScaledColumn_below
    (coeffs rows : Array (Array Int)) (n k i : Nat)
    (hki : k < i) (hi : i < n)
    (hrow : i < coeffs.size) (hcol : k < coeffs[i]!.size) :
    getArrayEntry (writeScaledColumn coeffs rows n k) i k =
      getArrayEntry rows i k := by
  unfold writeScaledColumn
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  have hmem : i ∈ List.range' (k + 1) (n - (k + 1)) := by
    rw [List.mem_range']
    exact ⟨i - (k + 1), by omega, by omega⟩
  have hnodup : (List.range' (k + 1) (n - (k + 1))).Nodup := List.nodup_range'
  have hrow' : i < (setArrayEntry coeffs k k (getArrayEntry rows k k)).size := by
    simp [setArrayEntry, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hrow]
  have hcol' :
      k < (setArrayEntry coeffs k k (getArrayEntry rows k k))[i]!.size := by
    unfold setArrayEntry
    rw [array_getElem!_set!_ne _ (show i ≠ k by omega)]
    exact hcol
  exact getArrayEntry_foldl_setArrayEntry_col_mem
    (List.range' (k + 1) (n - (k + 1)))
    (setArrayEntry coeffs k k (getArrayEntry rows k k)) rows k i
    hmem hnodup hrow' hcol'

/-- `writeScaledColumn` only updates entries in column `k`; entries in any
other column are unchanged. -/
private theorem getArrayEntry_writeScaledColumn
    (coeffs rows : Array (Array Int)) (n k r c : Nat) (hc : c ≠ k) :
    getArrayEntry (writeScaledColumn coeffs rows n k) r c =
      getArrayEntry coeffs r c := by
  unfold writeScaledColumn
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [getArrayEntry_foldl_setArrayEntry_col_ne _ _ _ _ _ _ hc]
  by_cases hrow : r = k
  · subst r
    rw [getArrayEntry_setArrayEntry_of_col_ne _ _ _ _ _ hc]
  · rw [getArrayEntry_setArrayEntry_of_row_ne]
    exact hrow

/-- A `foldl` of `setArrayEntry` writes at column `k` preserves the
outer-array size. -/
private theorem foldl_setArrayEntry_size
    (xs : List Nat) (init rows : Array (Array Int)) (k : Nat) :
    (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) init).size =
      init.size := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact setArrayEntry_size _ _ _ _

/-- A `foldl` of `setArrayEntry` writes at column `k` preserves inner row sizes. -/
private theorem foldl_setArrayEntry_rows_size
    (xs : List Nat) (init rows : Array (Array Int)) (k r : Nat) :
    (xs.foldl (fun next x => setArrayEntry next x k (getArrayEntry rows x k)) init)[r]!.size =
      init[r]!.size := by
  induction xs generalizing init with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact setArrayEntry_rows_size _ _ _ _ _

/-- `writeScaledColumn` preserves the outer-array size. -/
private theorem writeScaledColumn_size
    (coeffs rows : Array (Array Int)) (n k : Nat) :
    (writeScaledColumn coeffs rows n k).size = coeffs.size := by
  unfold writeScaledColumn
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [foldl_setArrayEntry_size]
  exact setArrayEntry_size _ _ _ _

/-- `writeScaledColumn` preserves each inner row's size. -/
private theorem writeScaledColumn_rows_size
    (coeffs rows : Array (Array Int)) (n k r : Nat) :
    (writeScaledColumn coeffs rows n k)[r]!.size = coeffs[r]!.size := by
  unfold writeScaledColumn
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size]
  rw [foldl_setArrayEntry_rows_size]
  exact setArrayEntry_rows_size _ _ _ _ _

/-- Every entry of the default (empty) integer array reads back as `0`. -/
private theorem getArrayEntry_default_row (j : Nat) :
    (default : Array Int)[j]! = 0 := by
  rfl

@[expose]
def stepScaledRows (rows : Array (Array Int)) (n k : Nat)
    (pivot prevPivot : Int) : Array (Array Int) :=
  Id.run do
    let mut next := rows
    let pivotRow := rows[k]!
    for i in [k + 1:n] do
      next := next.modify i fun sourceRow =>
        let entryIK := sourceRow[k]!
        Id.run do
          let mut nextRow := sourceRow.set! k 0
          for j in [k + 1:n] do
            let value :=
              Matrix.exactDiv
                (pivot * nextRow[j]! - entryIK * pivotRow[j]!) prevPivot
            nextRow := nextRow.set! j value
          return nextRow
    return next

section StepScaledRowsBookkeeping

/-- After one `stepScaledRows` sweep, rows whose index lies at or below the
current pivot are untouched by the outer fold. -/
private theorem getArrayEntry_stepScaledRows_of_row_le
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (r c : Nat) (hr : r ≤ k) :
    getArrayEntry (stepScaledRows rows n k pivot prevPivot) r c =
      getArrayEntry rows r c := by
  show
      (stepScaledRows rows n k pivot prevPivot)[r]![c]! =
        rows[r]![c]!
  unfold stepScaledRows
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    -Array.set!_eq_setIfInBounds]
  have hnot : r ∉ List.range' (k + 1) (n - (k + 1)) := by
    intro hmem
    rw [List.mem_range'] at hmem
    obtain ⟨i, hi, hri⟩ := hmem
    omega
  rw [getElem!_foldl_modify_of_notMem _ _ _ _ hnot]

/-- The new row written at trailing index `r` (with `k < r` and `r < n`) by
`stepScaledRows`, expressed in fold form. This is an intermediate
characterisation; downstream lemmas read individual entries via
`getElem!_foldl_set!_*`. -/
private theorem stepScaledRows_row_at_trailing
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (r : Nat) (hk : k < r) (hr : r < n) (hrows : r < rows.size) :
    (stepScaledRows rows n k pivot prevPivot)[r]! =
      (List.range' (k + 1) (n - (k + 1))).foldl
        (fun nextRow j =>
          nextRow.set! j
            (Matrix.exactDiv
              (pivot * nextRow[j]! - rows[r]![k]! * getArrayEntry rows k j)
              prevPivot))
        (rows[r]!.set! k 0) := by
  unfold stepScaledRows
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    -Array.set!_eq_setIfInBounds]
  have hmem : r ∈ List.range' (k + 1) (n - (k + 1)) := by
    rw [List.mem_range']
    exact ⟨r - (k + 1), by omega, by omega⟩
  have hnodup : (List.range' (k + 1) (n - (k + 1))).Nodup := List.nodup_range'
  rw [getElem!_foldl_modify_of_mem_nodup _ _ _ _ hmem hnodup hrows]
  simp [getArrayEntry]

/-- The pivot column of `stepScaledRows` is cleared at every trailing row. -/
private theorem getArrayEntry_stepScaledRows_pivot_col
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (r : Nat) (hk : k < r) (hr : r < n) (hrows : r < rows.size)
    (hk_row : k < rows[r]!.size) :
    getArrayEntry (stepScaledRows rows n k pivot prevPivot) r k = 0 := by
  show (stepScaledRows rows n k pivot prevPivot)[r]![k]! = 0
  rw [stepScaledRows_row_at_trailing rows n k pivot prevPivot r hk hr hrows]
  have hnot : k ∉ List.range' (k + 1) (n - (k + 1)) := by
    intro hmem
    rw [List.mem_range'] at hmem
    obtain ⟨i, hi, hki⟩ := hmem
    omega
  rw [getElem!_foldl_setSelf_of_notMem
    (f := fun j entry =>
      Matrix.exactDiv (pivot * entry - rows[r]![k]! * getArrayEntry rows k j) prevPivot)
    _ _ _ hnot]
  grind

/-- Trailing-column entries of `stepScaledRows` are the fraction-free
Bareiss-style update written by the inner sweep. -/
private theorem getArrayEntry_stepScaledRows_trailing
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (r c : Nat) (hkr : k < r) (hr : r < n) (hkc : k < c) (hc : c < n)
    (hrows : r < rows.size) (hcols : c < rows[r]!.size) :
    getArrayEntry (stepScaledRows rows n k pivot prevPivot) r c =
      Matrix.exactDiv
        (pivot * rows[r]![c]! - rows[r]![k]! * getArrayEntry rows k c)
        prevPivot := by
  show
      (stepScaledRows rows n k pivot prevPivot)[r]![c]! =
        Matrix.exactDiv
          (pivot * rows[r]![c]! - rows[r]![k]! * getArrayEntry rows k c)
          prevPivot
  rw [stepScaledRows_row_at_trailing rows n k pivot prevPivot r hkr hr hrows]
  have hmem : c ∈ List.range' (k + 1) (n - (k + 1)) := by
    rw [List.mem_range']
    exact ⟨c - (k + 1), by omega, by omega⟩
  have hnodup : (List.range' (k + 1) (n - (k + 1))).Nodup := List.nodup_range'
  have hbound : c < (rows[r]!.set! k 0).size := by
    simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hcols]
  rw [getElem!_foldl_setSelf_of_mem_nodup
    (f := fun j entry =>
      Matrix.exactDiv (pivot * entry - rows[r]![k]! * getArrayEntry rows k j) prevPivot)
    _ _ _ hmem hnodup hbound]
  have hck : c ≠ k := by omega
  grind

/-- Entries strictly left of the pivot column of `stepScaledRows` are
preserved at every trailing row: the inner sweep only writes the trailing
window `[k+1, n)`, and the explicit pivot-column zeroing only touches
column `k`. -/
private theorem getArrayEntry_stepScaledRows_of_col_lt
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (r c : Nat) (hkr : k < r) (hr : r < n) (hc : c < k)
    (hrows : r < rows.size) :
    getArrayEntry (stepScaledRows rows n k pivot prevPivot) r c =
      getArrayEntry rows r c := by
  show
      (stepScaledRows rows n k pivot prevPivot)[r]![c]! = rows[r]![c]!
  rw [stepScaledRows_row_at_trailing rows n k pivot prevPivot r hkr hr hrows]
  have hnot : c ∉ List.range' (k + 1) (n - (k + 1)) := by
    intro hmem
    rw [List.mem_range'] at hmem
    obtain ⟨i, hi, hci⟩ := hmem
    omega
  rw [getElem!_foldl_setSelf_of_notMem
    (f := fun j entry =>
      Matrix.exactDiv (pivot * entry - rows[r]![k]! * getArrayEntry rows k j) prevPivot)
    _ _ _ hnot]
  have hck : c ≠ k := by omega
  grind

/-- The outer-array length of `stepScaledRows` matches the input. The outer
fold only replaces rows already present in `rows` via `Array.set!`, which
preserves array size. -/
private theorem stepScaledRows_size
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int) :
    (stepScaledRows rows n k pivot prevPivot).size = rows.size := by
  unfold stepScaledRows
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    -Array.set!_eq_setIfInBounds]
  exact size_foldl_modify _ _ _

/-- If the input row storage has the expected square shape, one
`stepScaledRows` sweep preserves every in-bounds row length. -/
private theorem stepScaledRows_rows_size
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (hsize : rows.size = n)
    (hrowsize : ∀ r, r < n → rows[r]!.size = n) :
    ∀ r, r < n → (stepScaledRows rows n k pivot prevPivot)[r]!.size = n := by
  intro r hr
  unfold stepScaledRows
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    -Array.set!_eq_setIfInBounds]
  let xs := List.range' (k + 1) (n - (k + 1))
  let f : Nat → Array Int → Array Int := fun i sourceRow =>
    (List.range' (k + 1) (n - (k + 1))).foldl
      (fun nextRow j =>
        nextRow.set! j
          (Matrix.exactDiv
            (pivot * nextRow[j]! - sourceRow[k]! * rows[k]![j]!)
            prevPivot))
      (sourceRow.set! k 0)
  by_cases hmem : r ∈ xs
  · have hnodup : xs.Nodup := by
      dsimp [xs]
      exact List.nodup_range'
    have hbound : r < rows.size := by
      rw [hsize]
      exact hr
    rw [getElem!_foldl_modify_of_mem_nodup xs rows f r hmem hnodup hbound]
    dsimp [f]
    have hinner_size :=
      size_foldl_setSelf
        (List.range' (k + 1) (n - (k + 1)))
        (rows[r]!.set! k 0)
        (fun j nextEntry =>
          Matrix.exactDiv
            (pivot * nextEntry - rows[r]![k]! * getArrayEntry rows k j)
            prevPivot)
    simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds,
      hrowsize r hr] at hinner_size ⊢
    exact hinner_size
  · rw [getElem!_foldl_modify_of_notMem xs rows f r hmem]
    exact hrowsize r hr

/-- Per-entry correspondence between the row-mutating array-storage
`stepScaledRows` update and the matrix-storage `Matrix.stepMatrix` update.
Trailing-block entries use the same `Matrix.exactDiv` expression, the pivot
column clears to zero, and entries outside the update region are preserved on
both sides. -/
private theorem getArrayEntry_stepScaledRows_matches_stepMatrix
    {n : Nat} (rows : Array (Array Int)) (M : Matrix Int n n) (k : Nat)
    (pivot prevPivot : Int)
    (hentry : ∀ a b : Fin n, getArrayEntry rows a.val b.val = M[a][b])
    (hsize : rows.size = n)
    (hrowsize : ∀ (a : Nat), a < n → rows[a]!.size = n)
    (i j : Fin n) :
    getArrayEntry (stepScaledRows rows n k pivot prevPivot) i.val j.val =
      (Matrix.stepMatrix M k pivot prevPivot)[i][j] := by
  rcases Nat.lt_or_ge k i.val with hki | hki
  · rcases Nat.lt_or_ge k j.val with hkj | hkj
    · -- Trailing-block update: divide the Bareiss numerator by `prevPivot`.
      have hrows : i.val < rows.size := by rw [hsize]; exact i.isLt
      have hcols : j.val < rows[i.val]!.size := by
        rw [hrowsize i.val i.isLt]; exact j.isLt
      have hij_eq : getArrayEntry rows i.val j.val = M[i][j] := hentry i j
      have hcol_eq :
          getArrayEntry rows i.val k =
            M[i][(⟨k, Nat.lt_trans hki i.isLt⟩ : Fin n)] := by
        simpa using hentry i ⟨k, Nat.lt_trans hki i.isLt⟩
      have hrow_eq :
          getArrayEntry rows k j.val =
            M[(⟨k, Nat.lt_trans hkj j.isLt⟩ : Fin n)][j] := by
        simpa using hentry ⟨k, Nat.lt_trans hkj j.isLt⟩ j
      rw [getArrayEntry_stepScaledRows_trailing rows n k pivot prevPivot
            i.val j.val hki i.isLt hkj j.isLt hrows hcols]
      rw [Matrix.stepMatrix_update_eq M k pivot prevPivot i j hki hkj]
      change Matrix.exactDiv
          (pivot * getArrayEntry rows i.val j.val -
            getArrayEntry rows i.val k * getArrayEntry rows k j.val) prevPivot =
        Matrix.exactDiv
          (pivot * M[i][j] -
            M[i][(⟨k, Nat.lt_trans hki i.isLt⟩ : Fin n)] *
              M[(⟨k, Nat.lt_trans hkj j.isLt⟩ : Fin n)][j]) prevPivot
      rw [hij_eq, hcol_eq, hrow_eq]
    · -- Pivot column or strictly-left column at a trailing row.
      rcases Nat.lt_or_eq_of_le hkj with hkj_lt | hkj_eq
      · -- Strictly left of pivot column: entries preserved on both sides.
        have hrows : i.val < rows.size := by rw [hsize]; exact i.isLt
        rw [getArrayEntry_stepScaledRows_of_col_lt rows n k pivot prevPivot
              i.val j.val hki i.isLt hkj_lt hrows]
        rw [Matrix.stepMatrix_eq_of_not_update M k pivot prevPivot i j
              (fun h => Nat.not_lt_of_ge hkj h.2)
              (fun h => Nat.ne_of_lt hkj_lt h.2)]
        exact hentry i j
      · -- Pivot column itself: both sides clear to zero.
        have hjk : j.val = k := hkj_eq
        have hrows : i.val < rows.size := by rw [hsize]; exact i.isLt
        have hk_row : k < rows[i.val]!.size := by
          rw [hrowsize i.val i.isLt]
          exact Nat.lt_of_lt_of_le hki (Nat.le_of_lt i.isLt)
        have hLHS :
            getArrayEntry (stepScaledRows rows n k pivot prevPivot) i.val j.val = 0 := by
          rw [hjk]
          exact getArrayEntry_stepScaledRows_pivot_col rows n k pivot prevPivot
            i.val hki i.isLt hrows hk_row
        have hRHS :
            (Matrix.stepMatrix M k pivot prevPivot)[i][j] = 0 :=
          Matrix.stepMatrix_pivot_col_below M k pivot prevPivot i j hki hjk
        rw [hLHS]
        exact hRHS.symm
  · -- Row preserved: at or above pivot row.
    rw [getArrayEntry_stepScaledRows_of_row_le rows n k pivot prevPivot
          i.val j.val hki]
    rw [Matrix.stepMatrix_eq_of_not_update M k pivot prevPivot i j
          (fun h => Nat.not_lt_of_ge hki h.1)
          (fun h => Nat.not_lt_of_ge hki h.1)]
    exact hentry i j

/-- Matrix-level correspondence: one row-mutating `stepScaledRows` array
update, viewed as a matrix via `rowsToMatrix`, equals the corresponding
`Matrix.stepMatrix` update on the matrix view of the same row storage. -/
private theorem rowsToMatrix_stepScaledRows_eq
    {n : Nat} (rows : Array (Array Int)) (k : Nat) (pivot prevPivot : Int)
    (hsize : rows.size = n)
    (hrowsize : ∀ (a : Nat), a < n → rows[a]!.size = n) :
    rowsToMatrix (stepScaledRows rows n k pivot prevPivot) n =
      Matrix.stepMatrix (rowsToMatrix rows n) k pivot prevPivot := by
  apply Hex.Matrix.ext
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  have hentry : ∀ a b : Fin n,
      getArrayEntry rows a.val b.val = (rowsToMatrix rows n)[a][b] := by
    intro a b
    simp [rowsToMatrix, Matrix.ofFn]
  simpa [rowsToMatrix, Matrix.ofFn, Hex.Matrix.getRow, Fin.getElem_fin] using
    getArrayEntry_stepScaledRows_matches_stepMatrix rows (rowsToMatrix rows n)
      k pivot prevPivot hentry hsize hrowsize ⟨i, hi⟩ ⟨j, hj⟩

end StepScaledRowsBookkeeping

@[expose]
def scaledCoeffArrayLoop (n fuel : Nat) (state : ScaledCoeffArrayState) :
    ScaledCoeffArrayState :=
  match fuel with
  | 0 => state
  | fuel + 1 =>
      if state.step < n then
        let k := state.step
        let coeffs := writeScaledColumn state.coeffs state.matrix n k
        let pivot := getArrayEntry state.matrix k k
        if k + 1 < n then
          if pivot = 0 then
            { state with coeffs := coeffs }
          else
            let next : ScaledCoeffArrayState :=
              { step := state.step + 1
                matrix := stepScaledRows state.matrix n k pivot state.prevPivot
                coeffs := coeffs
                prevPivot := pivot }
            scaledCoeffArrayLoop n fuel next
        else
          { state with step := state.step + 1, coeffs := coeffs }
      else
        state

private theorem getArrayEntry_zeroRows (n i j : Nat) :
    getArrayEntry (zeroRows n) i j = 0 := by
  by_cases hi : i < n
  · by_cases hj : j < n <;> simp [zeroRows, getArrayEntry, hi, hj]
  · simp [zeroRows, getArrayEntry, hi, getArrayEntry_default_row]

/-- Outer-array length of the initial Gram row buffer. -/
private theorem gramRows_size (b : Matrix Int n m) : (gramRows b).size = n := by
  simp [gramRows]

/-- Inner-row length of each row of the initial Gram row buffer. -/
private theorem gramRows_row_size (b : Matrix Int n m) (r : Nat) (hr : r < n) :
    (gramRows b)[r]!.size = n := by
  simp [gramRows, hr]

/-- Outer-array length of the initial coefficient buffer. -/
private theorem zeroRows_size (n : Nat) : (zeroRows n).size = n := by
  simp [zeroRows]

/-- Inner-row length of each row of the initial coefficient buffer. -/
private theorem zeroRows_row_size (n : Nat) (r : Nat) (hr : r < n) :
    (zeroRows n)[r]!.size = n := by
  simp [zeroRows, hr]

private theorem getArrayEntry_scaledCoeffArrayLoop_above
    (n fuel : Nat) (state : ScaledCoeffArrayState)
    (hcoeffs : ∀ i j, i < j → getArrayEntry state.coeffs i j = 0)
    (i j : Nat) (hij : i < j) :
    getArrayEntry (scaledCoeffArrayLoop n fuel state).coeffs i j = 0 := by
  induction fuel generalizing state with
  | zero =>
      exact hcoeffs i j hij
  | succ fuel ih =>
      rw [scaledCoeffArrayLoop]
      by_cases hstep : state.step < n
      · simp only [hstep, ↓reduceIte]
        by_cases hnext : state.step + 1 < n
        · simp only [hnext, ↓reduceIte]
          by_cases hpivot : getArrayEntry state.matrix state.step state.step = 0
          · simp only [hpivot, ↓reduceIte]
            rw [getArrayEntry_writeScaledColumn_above _ _ _ _ _ _ hij]
            exact hcoeffs i j hij
          · simp only [hpivot, ↓reduceIte]
            exact ih
              { step := state.step + 1
                matrix := stepScaledRows state.matrix n state.step
                  (getArrayEntry state.matrix state.step state.step) state.prevPivot
                coeffs := writeScaledColumn state.coeffs state.matrix n state.step
                prevPivot := getArrayEntry state.matrix state.step state.step }
              (by
                intro r c hrc
                rw [getArrayEntry_writeScaledColumn_above _ _ _ _ _ _ hrc]
                exact hcoeffs r c hrc)
        · simp only [hnext, ↓reduceIte]
          rw [getArrayEntry_writeScaledColumn_above _ _ _ _ _ _ hij]
          exact hcoeffs i j hij
      · simp only [hstep, ↓reduceIte]
        exact hcoeffs i j hij

/-- Once a coefficient column lies strictly before the current loop step, later
`scaledCoeffArrayLoop` iterations do not rewrite that column. -/
private theorem getArrayEntry_scaledCoeffArrayLoop_preserve_col_before_step
    (n fuel : Nat) (state : ScaledCoeffArrayState) (i j : Nat)
    (hj : j < state.step) :
    getArrayEntry (scaledCoeffArrayLoop n fuel state).coeffs i j =
      getArrayEntry state.coeffs i j := by
  induction fuel generalizing state with
  | zero =>
      rfl
  | succ fuel ih =>
      rw [scaledCoeffArrayLoop]
      by_cases hstep : state.step < n
      · simp only [hstep, ↓reduceIte]
        by_cases hnext : state.step + 1 < n
        · simp only [hnext, ↓reduceIte]
          by_cases hpivot : getArrayEntry state.matrix state.step state.step = 0
          · simp only [hpivot, ↓reduceIte]
            rw [getArrayEntry_writeScaledColumn]
            omega
          · simp only [hpivot, ↓reduceIte]
            rw [ih]
            · rw [getArrayEntry_writeScaledColumn]
              omega
            · show j < state.step + 1
              omega
        · simp only [hnext, ↓reduceIte]
          rw [getArrayEntry_writeScaledColumn]
          omega
      · simp only [hstep, ↓reduceIte]

/-- Run one no-pivot fraction-free Gram elimination and record each scaled
coefficient column immediately before the elimination step zeroes it.

This is the **reference formulation** of the scaled-coefficient matrix, kept
for proofs rather than execution. The live algorithm runs `scaledCoeffRowsSchur`
(the per-row Schur recurrence below); `getArrayEntry_scaledCoeffRowsSchur_eq`
proves the two agree entry-for-entry, and that bridge is what connects
`scaledCoeffRowsSchur` to `gramDet` / `scaledCoeffs`. Do not remove this
formulation as "unused": deleting it breaks the correctness proof of the live
path. -/
@[expose]
def scaledCoeffRows (b : Matrix Int n m) : Array (Array Int) :=
  let state :=
    scaledCoeffArrayLoop n n
      { step := 0
        matrix := gramRows b
        coeffs := zeroRows n
        prevPivot := 1 }
  state.coeffs

/-- Schur-complement σ-chain for the fraction-free scaled Gram-Schmidt
recurrence. Each step divides by the previous diagonal pivot `rows[p-1][p-1]`
via `Matrix.exactDiv`; that division is **exact** — the fraction-free Bareiss
invariant guarantees the numerator is divisible by the pivot, so `sigma` stays
an integer bounded by a minor determinant rather than growing as an unreduced
fraction. -/
@[expose]
def schurSigma (rows : Array (Array Int)) (i j : Nat) : Int :=
  Id.run do
    let mut sigma := getArrayEntry rows i 0 * getArrayEntry rows j 0
    for p in [1:j] do
      sigma :=
        Matrix.exactDiv
          (getArrayEntry rows p p * sigma +
            getArrayEntry rows i p * getArrayEntry rows j p)
          (getArrayEntry rows (p - 1) (p - 1))
    return sigma

@[expose]
def schurScaledCoeffEntry
    (rows gram : Array (Array Int)) (i j : Nat) : Int :=
  if j = 0 then
    getArrayEntry gram i 0
  else
    getArrayEntry rows (j - 1) (j - 1) * getArrayEntry gram i j -
      schurSigma rows i j

/-- Per-row Schur-complement scaled Gram-Schmidt coefficient kernel.

Rows are filled from top to bottom; within row `i`, entries `0..i` are written
left to right.  For `j < i` this writes the scaled coefficient `ν[i][j]`; for
`j = i` the same recurrence writes the diagonal Gram determinant `d_{i+1}`. -/
@[expose]
def scaledCoeffRowsSchur (b : Matrix Int n m) : Array (Array Int) :=
  Id.run do
    let gram := gramRows b
    let mut rows := zeroRows n
    for i in [0:n] do
      for j in [0:i + 1] do
        rows := setArrayEntry rows i j (schurScaledCoeffEntry rows gram i j)
    return rows

private theorem getArrayEntry_schurColumnLoop_upper
    (cols : List Nat) (rows gram : Array (Array Int)) (row i j : Nat)
    (hij : i < j) (hcols : ∀ c ∈ cols, c ≤ row) :
    getArrayEntry
        (cols.foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col)) rows)
        i j =
      getArrayEntry rows i j := by
  induction cols generalizing rows with
  | nil =>
      simp
  | cons col cols ih =>
      simp only [List.foldl_cons]
      have hcols_tail : ∀ c ∈ cols, c ≤ row := by
        intro c hc
        exact hcols c (List.mem_cons_of_mem col hc)
      rw [ih _ hcols_tail]
      by_cases hrow : i = row
      · subst row
        have hcol_le : col ≤ i := hcols col (by simp)
        rw [getArrayEntry_setArrayEntry_of_col_ne]
        omega
      · rw [getArrayEntry_setArrayEntry_of_row_ne]
        exact hrow

private theorem getArrayEntry_schurRowLoop_upper
    (rowList : List Nat) (rows gram : Array (Array Int)) (i j : Nat)
    (hij : i < j) :
    getArrayEntry
        (rowList.foldl
          (fun next row =>
            (List.range' 0 (row + 1)).foldl
              (fun next col =>
                setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
              next) rows)
        i j =
      getArrayEntry rows i j := by
  induction rowList generalizing rows with
  | nil =>
      simp
  | cons row rowList ih =>
      simp only [List.foldl_cons]
      rw [ih _, getArrayEntry_schurColumnLoop_upper]
      · exact hij
      · intro c hc
        rw [List.mem_range'] at hc
        omega

private theorem getArrayEntry_scaledCoeffRowsSchur_upper
    (b : Matrix Int n m) (i j : Nat) (hij : i < j) :
    getArrayEntry (scaledCoeffRowsSchur b) i j = 0 := by
  simp [scaledCoeffRowsSchur]
  rw [getArrayEntry_schurRowLoop_upper]
  · exact getArrayEntry_zeroRows n i j
  · exact hij

/-- The Schur column loop fixes the active row `row`: cells in any other row
are untouched, irrespective of which columns the loop visits. -/
private theorem getArrayEntry_schurColumnLoop_row_ne
    (cols : List Nat) (rows gram : Array (Array Int)) (row r c : Nat)
    (hr : r ≠ row) :
    getArrayEntry
        (cols.foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col)) rows)
        r c =
      getArrayEntry rows r c := by
  induction cols generalizing rows with
  | nil => simp
  | cons col cols ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact getArrayEntry_setArrayEntry_of_row_ne rows row col r c _ hr

/-- Row-completion frame lemma. The outer Schur row loop only writes to rows
listed in `rowList`; cells in rows not in `rowList` retain their initial
values. In particular, once row `i` has been processed by the row loop, the
remaining row iterations preserve every cell `(i, ·)`. -/
private theorem getArrayEntry_schurRowLoop_row_not_mem
    (rowList : List Nat) (rows gram : Array (Array Int)) (i j : Nat)
    (hi : i ∉ rowList) :
    getArrayEntry
        (rowList.foldl
          (fun next row =>
            (List.range' 0 (row + 1)).foldl
              (fun next col =>
                setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
              next) rows)
        i j =
      getArrayEntry rows i j := by
  induction rowList generalizing rows with
  | nil => simp
  | cons row rowList ih =>
      simp only [List.foldl_cons]
      have hi_ne : i ≠ row := fun h => hi (h ▸ List.mem_cons_self)
      have hi_tail : i ∉ rowList := fun h => hi (List.mem_cons_of_mem row h)
      rw [ih _ hi_tail]
      exact getArrayEntry_schurColumnLoop_row_ne _ rows gram row i j hi_ne

/-- Column-loop stability for the `(row, 0)` cell when the loop never visits
column `0`. Subsequent column writes at a different column keep the cell
unchanged. -/
private theorem getArrayEntry_schurColumnLoop_col_zero_preserve
    (cols : List Nat) (rows gram : Array (Array Int)) (row : Nat)
    (hzero : 0 ∉ cols) :
    getArrayEntry
        (cols.foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col)) rows)
        row 0 =
      getArrayEntry rows row 0 := by
  induction cols generalizing rows with
  | nil => simp
  | cons col cols ih =>
      simp only [List.foldl_cons]
      have h_col_ne : col ≠ 0 := fun h => hzero (h ▸ List.mem_cons_self)
      have h_tail : 0 ∉ cols := fun h => hzero (List.mem_cons_of_mem col h)
      rw [ih _ h_tail]
      exact getArrayEntry_setArrayEntry_of_col_ne rows row col 0 _ h_col_ne.symm

/-- Column-loop stability for a cell `(row, col_target)` when the loop never
visits `col_target`. Subsequent column writes at different columns keep
the cell unchanged. -/
private theorem getArrayEntry_schurColumnLoop_col_not_mem
    (cols : List Nat) (rows gram : Array (Array Int)) (row col_target : Nat)
    (h_not_mem : col_target ∉ cols) :
    getArrayEntry
        (cols.foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col)) rows)
        row col_target =
      getArrayEntry rows row col_target := by
  induction cols generalizing rows with
  | nil => simp
  | cons col cols ih =>
      simp only [List.foldl_cons]
      have h_col_ne : col ≠ col_target :=
        fun h => h_not_mem (h ▸ List.mem_cons_self)
      have h_tail : col_target ∉ cols :=
        fun h => h_not_mem (List.mem_cons_of_mem col h)
      rw [ih _ h_tail]
      exact getArrayEntry_setArrayEntry_of_col_ne rows row col col_target _
        (fun h => h_col_ne h.symm)

/-- Single-row column-loop dispatch for column `0`. When `0` appears in
`cols`, the column loop ultimately writes `getArrayEntry gram row 0` into the
`(row, 0)` slot. Because the `j = 0` branch of `schurScaledCoeffEntry`
returns the gram entry directly, this value is independent of which other
columns are written before or after. -/
private theorem getArrayEntry_schurColumnLoop_col_zero
    (cols : List Nat) (rows gram : Array (Array Int)) (row : Nat)
    (hzero : 0 ∈ cols)
    (hrow : row < rows.size) (hcol : 0 < rows[row]!.size) :
    getArrayEntry
        (cols.foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col)) rows)
        row 0 =
      getArrayEntry gram row 0 := by
  induction cols generalizing rows with
  | nil => exact absurd hzero (List.not_mem_nil)
  | cons col cols ih =>
      simp only [List.foldl_cons]
      by_cases h_zero_in_tail : 0 ∈ cols
      · have hrow' :
            row < (setArrayEntry rows row col
                (schurScaledCoeffEntry rows gram row col)).size := by
          rw [setArrayEntry_size]; exact hrow
        have hcol' :
            0 < (setArrayEntry rows row col
                (schurScaledCoeffEntry rows gram row col))[row]!.size := by
          rw [setArrayEntry_rows_size]; exact hcol
        exact ih _ h_zero_in_tail hrow' hcol'
      · have h_col_eq : col = 0 := by
          rcases List.mem_cons.mp hzero with h | h
          · exact h.symm
          · exact (h_zero_in_tail h).elim
        subst h_col_eq
        rw [getArrayEntry_schurColumnLoop_col_zero_preserve _ _ _ _ h_zero_in_tail,
          getArrayEntry_setArrayEntry_self _ _ _ _ hrow hcol]
        simp [schurScaledCoeffEntry]

/-- Size preservation: the Schur column loop keeps the outer-array length. -/
private theorem schurColumnLoop_size
    (cols : List Nat) (rows gram : Array (Array Int)) (row : Nat) :
    (cols.foldl
        (fun next col =>
          setArrayEntry next row col (schurScaledCoeffEntry next gram row col)) rows).size =
      rows.size := by
  induction cols generalizing rows with
  | nil => rfl
  | cons col cols ih => simp only [List.foldl_cons]; rw [ih]; exact setArrayEntry_size _ _ _ _

/-- Size preservation: the Schur column loop keeps each inner row's length. -/
private theorem schurColumnLoop_rows_size
    (cols : List Nat) (rows gram : Array (Array Int)) (row r : Nat) :
    (cols.foldl
        (fun next col =>
          setArrayEntry next row col (schurScaledCoeffEntry next gram row col)) rows)[r]!.size =
      rows[r]!.size := by
  induction cols generalizing rows with
  | nil => rfl
  | cons col cols ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact setArrayEntry_rows_size _ _ _ _ _

/-- Size preservation: the Schur row loop keeps the outer-array length. -/
private theorem schurRowLoop_size
    (rowList : List Nat) (rows gram : Array (Array Int)) :
    (rowList.foldl
      (fun next row =>
        (List.range' 0 (row + 1)).foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
          next) rows).size =
      rows.size := by
  induction rowList generalizing rows with
  | nil => rfl
  | cons row rowList ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact schurColumnLoop_size _ _ _ _

/-- Size preservation: the Schur row loop keeps each inner row's length. -/
private theorem schurRowLoop_rows_size
    (rowList : List Nat) (rows gram : Array (Array Int)) (r : Nat) :
    (rowList.foldl
      (fun next row =>
        (List.range' 0 (row + 1)).foldl
          (fun next col =>
            setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
          next) rows)[r]!.size =
      rows[r]!.size := by
  induction rowList generalizing rows with
  | nil => rfl
  | cons row rowList ih =>
      simp only [List.foldl_cons]
      rw [ih]
      exact schurColumnLoop_rows_size _ _ _ _ _

/-- Outer-array length of the per-row Schur kernel: the row buffer is
allocated as `zeroRows n` and the row loop writes via `setArrayEntry`,
which preserves outer-array size. -/
private theorem scaledCoeffRowsSchur_size (b : Matrix Int n m) :
    (scaledCoeffRowsSchur b).size = n := by
  simp [scaledCoeffRowsSchur]
  rw [schurRowLoop_size]
  exact zeroRows_size n

/-- Row-loop dispatch for the `(i, 0)` boundary. If `i ∈ rowList` and the
initial row buffer is large enough at row `i`, the Schur row loop writes the
`(i, 0)` cell to `getArrayEntry gram i 0` (via the inner column loop) and
leaves it untouched in subsequent row iterations. -/
private theorem getArrayEntry_schurRowLoop_col_zero
    (rowList : List Nat) (rows gram : Array (Array Int)) (i : Nat)
    (hi : i ∈ rowList) (hrow : i < rows.size) (hcol : 0 < rows[i]!.size) :
    getArrayEntry
        (rowList.foldl
          (fun next row =>
            (List.range' 0 (row + 1)).foldl
              (fun next col =>
                setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
              next) rows)
        i 0 =
      getArrayEntry gram i 0 := by
  induction rowList generalizing rows with
  | nil => exact absurd hi List.not_mem_nil
  | cons row rowList ih =>
      simp only [List.foldl_cons]
      by_cases h_i_in_tail : i ∈ rowList
      · -- Recurse into the tail, deriving size hypotheses via the column-loop
        -- size-preservation lemmas.
        have h_size :
            i < ((List.range' 0 (row + 1)).foldl
              (fun next col =>
                setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
              rows).size := by
          rw [schurColumnLoop_size]; exact hrow
        have h_row_size :
            0 < ((List.range' 0 (row + 1)).foldl
              (fun next col =>
                setArrayEntry next row col (schurScaledCoeffEntry next gram row col))
              rows)[i]!.size := by
          rw [schurColumnLoop_rows_size]; exact hcol
        exact ih _ h_i_in_tail h_size h_row_size
      · -- i is exactly the current `row`. The column loop visits `0`
        -- (`List.range' 0 (row + 1)` contains `0`), writes the gram entry
        -- there, and tail row iterations preserve `(i, 0)`.
        have h_i_eq : i = row := by
          rcases List.mem_cons.mp hi with h | h
          · exact h
          · exact (h_i_in_tail h).elim
        subst h_i_eq
        rw [getArrayEntry_schurRowLoop_row_not_mem _ _ _ _ _ h_i_in_tail]
        apply getArrayEntry_schurColumnLoop_col_zero _ _ _ _ _ hrow hcol
        rw [List.mem_range']
        exact ⟨0, Nat.succ_pos _, by simp⟩

end GramSchmidt.Int
end Hex
