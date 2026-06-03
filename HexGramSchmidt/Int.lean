import HexGramSchmidt.Basic
import HexMatrix.Bareiss
import HexMatrix.Determinant

/-!
Executable Gram-determinant and scaled-coefficient definitions for
`hex-gram-schmidt`.

This module adds the determinant-driven integer surface that complements the
noncomputable basis/coefficient API from `HexGramSchmidt.Basic`: Gram
determinants of leading principal Gram minors, their vector packaging, and
the integral scaled Gram-Schmidt coefficient matrix used downstream by LLL.
-/
namespace Hex

namespace GramSchmidt

/-- Promote an index into a shorter prefix to the ambient matrix height. -/
def liftFinLE (i : Fin k) (hk : k ≤ n) : Fin n :=
  ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩

/-- Leading principal Gram matrix of the first `k` rows of an integer basis. -/
def leadingGramMatrixInt (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) : Matrix Int k k :=
  Matrix.ofFn fun i j =>
    Matrix.dot (b.row (liftFinLE i hk)) (b.row (liftFinLE j hk))

/-- The Gram-Schmidt leading Gram matrix is the leading prefix of the full
Gram matrix. This is the shape equation between the public `gramDet` API and
the one-pass `gramDetVec` implementation. -/
theorem leadingGramMatrixInt_eq_leadingPrefix_gram
    (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) :
    leadingGramMatrixInt b k hk =
      Matrix.leadingPrefix (Matrix.gramMatrix b) k hk := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simp [leadingGramMatrixInt, Matrix.leadingPrefix, Matrix.gramMatrix, Matrix.dot, Matrix.ofFn,
    liftFinLE]

/-- Leading principal Gram matrix of the first `k` rows of a rational basis. -/
def leadingGramMatrixRat (b : Matrix Rat n m) (k : Nat) (hk : k ≤ n) : Matrix Rat k k :=
  Matrix.ofFn fun i j =>
    Matrix.dot (b.row (liftFinLE i hk)) (b.row (liftFinLE j hk))

/-- Determinant matrix used by the integral `scaledCoeffs` entry formula:
take the leading `j + 1` Gram matrix and replace its last column by the inner
products with row `i`. -/
def scaledCoeffMatrix (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) :
    Matrix Int (j.val + 1) (j.val + 1) :=
  let hk : j.val + 1 ≤ n := Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt)
  Matrix.ofFn fun p q =>
    let p' := liftFinLE p hk
    if q.val = j.val then
      Matrix.dot (b.row p') (b.row i)
    else
      let q' := liftFinLE q hk
      Matrix.dot (b.row p') (b.row q')

end GramSchmidt

namespace GramSchmidt.Int

/-- Integer lattice membership in the row span of `b`. This mirrors the LLL
predicate without making `hex-gram-schmidt` depend on the downstream LLL
library. -/
def memLattice (b : Matrix Int n m) (v : Vector Int m) : Prop :=
  ∃ c : Vector Int n, Matrix.rowCombination b c = v

/-- The `k`-th Gram determinant: the determinant of the `k × k` leading
principal Gram matrix of the integer input. -/
def gramDet (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) : Nat :=
  (Matrix.bareiss (GramSchmidt.leadingGramMatrixInt b k hk)).toNat

/-- Linear independence of the row prefix determinants used by the
Gram-Schmidt theorem surface, stated over the Mathlib-free executable
`gramDet` data. -/
def independent (b : Matrix Int n m) : Prop :=
  ∀ k : Fin n, 0 < gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt)

/-- Product of the squared Gram-Schmidt basis norms along the first `k` rows. -/
noncomputable def gramSchmidtNormProduct (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) :
    Rat :=
  (List.finRange k).foldl
    (fun acc j =>
      let jn : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt hk⟩
      acc * Vector.normSq ((basis b).row jn))
    1

/-- Read a diagonal entry from a Bareiss elimination matrix as a natural
determinant value. -/
private def bareissDiagNat (data : Matrix.BareissData n) (r : Nat) (hr : r < n) : Nat :=
  let i : Fin n := ⟨r, hr⟩
  ((data.matrix.get i).get i).toNat

/-- Read the `k`-th leading-principal determinant from one no-pivot Bareiss
elimination pass over the full Gram matrix. This helper is only used for Gram
matrices: once a leading row prefix is singular, every larger leading prefix is
also singular, so all later leading determinants are zero. -/
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

private structure ScaledCoeffArrayState where
  step : Nat
  matrix : Array (Array Int)
  coeffs : Array (Array Int)
  prevPivot : Int

@[inline] def getArrayEntry (rows : Array (Array Int)) (row col : Nat) : Int :=
  rows[row]![col]!

private def zeroRows (n : Nat) : Array (Array Int) :=
  Array.replicate n (Array.replicate n 0)

private def gramRows (b : Matrix Int n m) : Array (Array Int) :=
  Array.ofFn fun i : Fin n =>
    Array.ofFn fun j : Fin n =>
      Matrix.dot (b.row i) (b.row j)

private theorem getArrayEntry_gramRows (b : Matrix Int n m) (i j : Fin n) :
    getArrayEntry (gramRows b) i.val j.val = (Matrix.gramMatrix b)[i][j] := by
  simp [getArrayEntry, gramRows, Matrix.gramMatrix, Matrix.dot, Matrix.ofFn]

def rowsToMatrix (rows : Array (Array Int)) (n : Nat) : Matrix Int n n :=
  Matrix.ofFn fun i j => getArrayEntry rows i.val j.val

private theorem rowsToMatrix_gramRows (b : Matrix Int n m) :
    rowsToMatrix (gramRows b) n = Matrix.gramMatrix b := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  simpa [rowsToMatrix, Matrix.ofFn] using
    getArrayEntry_gramRows b (⟨i, hi⟩ : Fin n) (⟨j, hj⟩ : Fin n)

private def setArrayEntry (rows : Array (Array Int)) (row col : Nat) (value : Int) :
    Array (Array Int) :=
  rows.set! row (rows[row]!.set! col value)

private theorem array_getElem!_set!_same {α : Type} [Inhabited α]
    (xs : Array α) {i : Nat} (hi : i < xs.size) (v : α) :
    (xs.set! i v)[i]! = v := by
  rw [Array.getElem!_eq_getD]
  simp [Array.getD, Array.set!_eq_setIfInBounds, hi]

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

private theorem getArrayEntry_setArrayEntry_of_row_ne
    (rows : Array (Array Int)) (row col r c : Nat) (value : Int) (hr : r ≠ row) :
    getArrayEntry (setArrayEntry rows row col value) r c = getArrayEntry rows r c := by
  grind [getArrayEntry, setArrayEntry]

private theorem getArrayEntry_setArrayEntry_of_col_ne
    (rows : Array (Array Int)) (row col c : Nat) (value : Int) (hc : c ≠ col) :
    getArrayEntry (setArrayEntry rows row col value) row c = getArrayEntry rows row c := by
  grind [getArrayEntry, setArrayEntry]

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
      rw [ih (setArrayEntry coeffs x k (getArrayEntry rows x k)) hxs']
      rw [getArrayEntry_setArrayEntry_of_row_ne]
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
      rw [ih (setArrayEntry coeffs x k (getArrayEntry rows x k)) hrxs]
      rw [getArrayEntry_setArrayEntry_of_row_ne]
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

/-- A `foldl` that sets indices appearing in `xs` leaves untouched indices
unchanged. Used to characterise the outer and inner sweeps of
`stepScaledRows`. -/
private theorem getElem!_foldl_set!_of_notMem
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α) (r : Nat)
    (hr : r ∉ xs) :
    (xs.foldl (fun next x => next.set! x (f x)) arr)[r]! = arr[r]! := by
  induction xs generalizing arr with
  | nil => simp
  | cons x xs ih =>
      have hx : r ≠ x := fun h => hr (h ▸ List.mem_cons_self)
      have hxs : r ∉ xs := fun h => hr (List.mem_cons_of_mem _ h)
      simp only [List.foldl_cons]
      rw [ih _ hxs]
      grind

/-- A `foldl` that sets indices appearing in a `Nodup` list `xs` writes the
final image `f r` at every member index `r` that is in-bounds for the input
array. Used to read trailing entries of `stepScaledRows`. -/
private theorem getElem!_foldl_set!_of_mem_nodup
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α) (r : Nat)
    (hr : r ∈ xs) (hnodup : xs.Nodup) (hbound : r < arr.size) :
    (xs.foldl (fun next x => next.set! x (f x)) arr)[r]! = f r := by
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
        rw [getElem!_foldl_set!_of_notMem _ _ _ _ hxnotmem]
        have hsize : r < (arr.set! r (f r)).size := by
          simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hbound]
        grind
      · have hbound' : r < (arr.set! x (f x)).size := by
          simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hbound]
        exact ih _ hr_in hnodup' hbound'

/-- A `foldl` that sets indices via `Array.set!` preserves the outer array
size. -/
private theorem size_foldl_set!
    {α : Type} [Inhabited α]
    (xs : List Nat) (arr : Array α) (f : Nat → α) :
    (xs.foldl (fun next x => next.set! x (f x)) arr).size = arr.size := by
  induction xs generalizing arr with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

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

private theorem modify_eq_set!
    {α : Type} [Inhabited α] (arr : Array α) (i : Nat) (f : α → α) :
    arr.modify i f = arr.set! i (f arr[i]!) := by
  by_cases h : i < arr.size
  · simp [Array.modify, Array.modifyM, Array.set!, Array.setIfInBounds, h]
  · simp [Array.modify, Array.modifyM, Array.set!, Array.setIfInBounds, h]

private theorem getElem!_modify_ne
    {α : Type} [Inhabited α] (arr : Array α) (i r : Nat) (f : α → α)
    (hr : r ≠ i) :
    (arr.modify i f)[r]! = arr[r]! := by
  rw [modify_eq_set!]
  grind

private theorem getElem!_modify_self
    {α : Type} [Inhabited α] (arr : Array α) (i : Nat) (f : α → α)
    (hi : i < arr.size) :
    (arr.modify i f)[i]! = f arr[i]! := by
  rw [modify_eq_set!]
  grind

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
        rw [ih _ hr_in hnodup' hbound']
        rw [getElem!_modify_ne arr x r (f x) hr_ne_x]

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

private def writeScaledColumn (coeffs rows : Array (Array Int)) (n k : Nat) :
    Array (Array Int) :=
  Id.run do
    let mut next := setArrayEntry coeffs k k (getArrayEntry rows k k)
    for i in [k + 1:n] do
      next := setArrayEntry next i k (getArrayEntry rows i k)
    return next

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
private theorem getArrayEntry_writeScaledColumn_of_col_ne
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

private theorem getArrayEntry_default_row (j : Nat) :
    (default : Array Int)[j]! = 0 := by
  rfl

private def stepScaledRows (rows : Array (Array Int)) (n k : Nat)
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
              Matrix.fmaDivExact pivot nextRow[j]! entryIK pivotRow[j]! prevPivot
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

/-- After one `stepScaledRows` sweep, rows whose index is past the matrix
extent are untouched by the outer fold (`Array.set!` is a no-op out of
bounds, and the iteration range stops at `n`). -/
private theorem getArrayEntry_stepScaledRows_of_row_ge
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (r c : Nat) (hr : n ≤ r) :
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
    Matrix.fmaDivExact,
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
          (Matrix.fmaDivExact pivot nextRow[j]! sourceRow[k]! rows[k]![j]!
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
          Matrix.fmaDivExact pivot nextEntry rows[r]![k]!
            (getArrayEntry rows k j) prevPivot)
    simpa [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds,
      hrowsize r hr] using hinner_size
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
private theorem rowsToMatrix_stepScaledRows_eq_stepMatrix
    {n : Nat} (rows : Array (Array Int)) (k : Nat) (pivot prevPivot : Int)
    (hsize : rows.size = n)
    (hrowsize : ∀ (a : Nat), a < n → rows[a]!.size = n) :
    rowsToMatrix (stepScaledRows rows n k pivot prevPivot) n =
      Matrix.stepMatrix (rowsToMatrix rows n) k pivot prevPivot := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  have hentry : ∀ a b : Fin n,
      getArrayEntry rows a.val b.val = (rowsToMatrix rows n)[a][b] := by
    intro a b
    simp [rowsToMatrix, Matrix.ofFn]
  simpa [rowsToMatrix, Matrix.ofFn] using
    getArrayEntry_stepScaledRows_matches_stepMatrix rows (rowsToMatrix rows n)
      k pivot prevPivot hentry hsize hrowsize ⟨i, hi⟩ ⟨j, hj⟩

/-- Local view of the canonical Bareiss array step: after reading the private
Gram-Schmidt row storage as a matrix, `Matrix.stepArray` is exactly
`Matrix.stepMatrix`. -/
private theorem rowsToMatrix_stepArray_eq_stepMatrix
    {n : Nat} (rows : Array (Array Int)) (k : Nat) (pivot prevPivot : Int) :
    rowsToMatrix (Matrix.stepArray rows n k pivot prevPivot) n =
      Matrix.stepMatrix (rowsToMatrix rows n) k pivot prevPivot := by
  simpa [rowsToMatrix, Matrix.rowsToMatrix, Matrix.ofFn, getArrayEntry, Matrix.getEntry] using
    Matrix.rowsToMatrix_stepArray (n := n) rows k pivot prevPivot

end StepScaledRowsBookkeeping

private def scaledCoeffArrayLoop (n fuel : Nat) (state : ScaledCoeffArrayState) :
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
            rw [getArrayEntry_writeScaledColumn_of_col_ne]
            omega
          · simp only [hpivot, ↓reduceIte]
            rw [ih]
            · rw [getArrayEntry_writeScaledColumn_of_col_ne]
              omega
            · show j < state.step + 1
              omega
        · simp only [hnext, ↓reduceIte]
          rw [getArrayEntry_writeScaledColumn_of_col_ne]
          omega
      · simp only [hstep, ↓reduceIte]

/-- If the array loop starts at column `state.step`, then the lower-triangle
entry written in that column is the current matrix-column value. In the regular
branch, the preservation lemma carries that captured column through the
remaining fuel. -/
private theorem getArrayEntry_scaledCoeffArrayLoop_capture_current_col
    (n fuel : Nat) (state : ScaledCoeffArrayState) (i : Nat)
    (hStep : state.step < n) (hji : state.step < i) (hi : i < n)
    (h_coeffs_size : state.coeffs.size = n)
    (h_coeffs_rows_size : ∀ r, r < n → state.coeffs[r]!.size = n) :
    getArrayEntry (scaledCoeffArrayLoop n (fuel + 1) state).coeffs i state.step =
      getArrayEntry state.matrix i state.step := by
  have hrow : i < state.coeffs.size := by
    rw [h_coeffs_size]; exact hi
  have hcol : state.step < state.coeffs[i]!.size := by
    rw [h_coeffs_rows_size i hi]; exact hStep
  rw [scaledCoeffArrayLoop]
  simp only [hStep, ↓reduceIte]
  by_cases hNext : state.step + 1 < n
  · simp only [hNext, ↓reduceIte]
    by_cases hpivot : getArrayEntry state.matrix state.step state.step = 0
    · simp only [hpivot, ↓reduceIte]
      exact getArrayEntry_writeScaledColumn_below state.coeffs state.matrix n
        state.step i hji hi hrow hcol
    · simp only [hpivot, ↓reduceIte]
      rw [getArrayEntry_scaledCoeffArrayLoop_preserve_col_before_step]
      · exact getArrayEntry_writeScaledColumn_below state.coeffs state.matrix n
          state.step i hji hi hrow hcol
      · show state.step < state.step + 1
        omega
  · simp only [hNext, ↓reduceIte]
    exact getArrayEntry_writeScaledColumn_below state.coeffs state.matrix n
      state.step i hji hi hrow hcol

/-- Matrix-state form of the current-column lower-triangle capture: for
aligned array and no-pivot states, the coefficient written at the current
column is exactly the pre-step matrix entry, not the later pivot-column value
after the next elimination step clears it. -/
private theorem scaledCoeffArrayLoop_lower_matches_current_step
    {state_array : ScaledCoeffArrayState} {state_matrix : Matrix.BareissState n}
    (h_step_eq : state_array.step = state_matrix.step)
    (h_matrix_eq : rowsToMatrix state_array.matrix n = state_matrix.matrix)
    (h_coeffs_size : state_array.coeffs.size = n)
    (h_coeffs_rows_size : ∀ r, r < n → state_array.coeffs[r]!.size = n)
    (fuel : Nat) (i : Fin n)
    (hji : state_matrix.step < i.val) :
    getArrayEntry (scaledCoeffArrayLoop n (fuel + 1) state_array).coeffs
        i.val state_array.step =
      state_matrix.matrix[i][
        (⟨state_matrix.step, Nat.lt_trans hji i.isLt⟩ : Fin n)] := by
  have hStepArray : state_array.step < n := by
    rw [h_step_eq]
    exact Nat.lt_trans hji i.isLt
  have hjiArray : state_array.step < i.val := by
    rw [h_step_eq]
    exact hji
  rw [getArrayEntry_scaledCoeffArrayLoop_capture_current_col n fuel state_array
    i.val hStepArray hjiArray i.isLt h_coeffs_size h_coeffs_rows_size]
  let col_array : Fin n := ⟨state_array.step, hStepArray⟩
  let col_matrix : Fin n := ⟨state_matrix.step, Nat.lt_trans hji i.isLt⟩
  have hcol_eq : col_array = col_matrix := Fin.ext h_step_eq
  have hentry :
      getArrayEntry state_array.matrix i.val state_array.step =
        (rowsToMatrix state_array.matrix n)[i][col_array] := by
    simp [rowsToMatrix, Matrix.ofFn, col_array]
  rw [hentry, h_matrix_eq]
  exact congrArg (fun c => state_matrix.matrix[i][c]) hcol_eq

/-- Base target-column form of lower-triangle capture. If the requested lower
column is exactly the starting no-pivot step, the scaled-coefficient loop
records the matrix entry from the pre-step `Matrix.noPivotLoop 0` state. -/
private theorem scaledCoeffArrayLoop_lower_matches_start_column
    {state_array : ScaledCoeffArrayState} {state_matrix : Matrix.BareissState n}
    (h_step_eq : state_array.step = state_matrix.step)
    (h_matrix_eq : rowsToMatrix state_array.matrix n = state_matrix.matrix)
    (h_coeffs_size : state_array.coeffs.size = n)
    (h_coeffs_rows_size : ∀ r, r < n → state_array.coeffs[r]!.size = n)
    (fuel : Nat) (i : Fin n)
    (hji : state_matrix.step < i.val) :
    getArrayEntry (scaledCoeffArrayLoop n (fuel + 1) state_array).coeffs
        i.val state_array.step =
      (Matrix.noPivotLoop 0 state_matrix).matrix[i][
        (⟨state_matrix.step, Nat.lt_trans hji i.isLt⟩ : Fin n)] := by
  simpa [Matrix.noPivotLoop_zero_fuel] using
    scaledCoeffArrayLoop_lower_matches_current_step
      (n := n) (state_array := state_array) (state_matrix := state_matrix)
      h_step_eq h_matrix_eq h_coeffs_size h_coeffs_rows_size fuel i hji

/-- Run one no-pivot fraction-free Gram elimination and record each scaled
coefficient column immediately before the elimination step zeroes it. -/
def scaledCoeffRows (b : Matrix Int n m) : Array (Array Int) :=
  let state :=
    scaledCoeffArrayLoop n n
      { step := 0
        matrix := gramRows b
        coeffs := zeroRows n
        prevPivot := 1 }
  state.coeffs

private def schurSigma (rows : Array (Array Int)) (i j : Nat) : Int :=
  Id.run do
    let mut sigma := getArrayEntry rows i 0 * getArrayEntry rows j 0
    for p in [1:j] do
      sigma :=
        Matrix.exactDiv
          (getArrayEntry rows p p * sigma +
            getArrayEntry rows i p * getArrayEntry rows j p)
          (getArrayEntry rows (p - 1) (p - 1))
    return sigma

private def schurScaledCoeffEntry
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
def scaledCoeffRowsSchur (b : Matrix Int n m) : Array (Array Int) :=
  Id.run do
    let gram := gramRows b
    let mut rows := zeroRows n
    for i in [0:n] do
      for j in [0:i + 1] do
        rows := setArrayEntry rows i j (schurScaledCoeffEntry rows gram i j)
    return rows

/-- Integral scaled Gram-Schmidt coefficients. For `j < i`, the entry is the
determinant formula corresponding to `d_{j+1} * μ_{i,j}`; on the diagonal we
store `d_{j+1}`, and entries above the diagonal are zero. -/
structure Data (n : Nat) where
  d : Vector Nat (n + 1)
  ν : Matrix Int n n

private def gramDetVecFromScaledCoeffRows (rows : Array (Array Int)) :
    Vector Nat (n + 1) :=
  Vector.ofFn fun k =>
    match hk : k.val with
    | 0 => 1
    | r + 1 =>
        have hrSucc : r + 1 < n + 1 := by
          simpa [hk] using k.isLt
        have _hr : r < n := Nat.succ_lt_succ_iff.mp hrSucc
        (getArrayEntry rows r r).toNat

/-- Run the per-row Schur scaled-coefficient kernel once and package both the
leading Gram determinant vector and the scaled Gram-Schmidt coefficient matrix. -/
def data (b : Matrix Int n m) : Data n :=
  let rows := scaledCoeffRowsSchur b
  { d := gramDetVecFromScaledCoeffRows rows
    ν := rowsToMatrix rows n }

/-- All leading Gram determinants, starting with the empty-prefix value
`d₀ = 1`. -/
def gramDetVec (b : Matrix Int n m) : Vector Nat (n + 1) :=
  (data b).d

/-- Integral scaled Gram-Schmidt coefficients. For `j < i`, the entry is the
determinant formula corresponding to `d_{j+1} * μ_{i,j}`; on the diagonal we
store `d_{j+1}`, and entries above the diagonal are zero. -/
def scaledCoeffs (b : Matrix Int n m) : Matrix Int n n :=
  (data b).ν

/-- Entry-level packaging equation from the public scaled-coefficient matrix
back to the shared array pass that computes it. -/
theorem scaledCoeffs_entry_eq_getArrayEntry
    (b : Matrix Int n m) (i j : Fin n) :
    GramSchmidt.entry (scaledCoeffs b) i j =
      getArrayEntry (scaledCoeffRowsSchur b) i.val j.val := by
  simp [scaledCoeffs, data, rowsToMatrix, GramSchmidt.entry, Matrix.row, Matrix.ofFn]

/-- One Bareiss update step commutes with taking the leading `K × K`
prefix: the leading prefix of the updated full matrix equals the result
of running the same step on the leading prefix. The pivot/`prevPivot`
scalars are passed through unchanged. -/
private theorem leadingPrefix_stepMatrix_eq
    {n K : Nat} (M : Matrix Int n n) (hK : K ≤ n)
    (k : Nat) (pivot prevPivot : Int) :
    Matrix.leadingPrefix (Matrix.stepMatrix M k pivot prevPivot) K hK =
      Matrix.stepMatrix (Matrix.leadingPrefix M K hK) k pivot prevPivot := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let iK : Fin K := ⟨i, hi⟩
  let jK : Fin K := ⟨j, hj⟩
  let iN : Fin n := ⟨i, Nat.lt_of_lt_of_le hi hK⟩
  let jN : Fin n := ⟨j, Nat.lt_of_lt_of_le hj hK⟩
  show (Matrix.leadingPrefix (Matrix.stepMatrix M k pivot prevPivot) K hK)[iK][jK] =
      (Matrix.stepMatrix (Matrix.leadingPrefix M K hK) k pivot prevPivot)[iK][jK]
  simp only [Matrix.leadingPrefix_entry]
  show (Matrix.stepMatrix M k pivot prevPivot)[iN][jN] =
      (Matrix.stepMatrix (Matrix.leadingPrefix M K hK) k pivot prevPivot)[iK][jK]
  by_cases htrail : k < i ∧ k < j
  · have hki_n : k < iN.val := htrail.1
    have hkj_n : k < jN.val := htrail.2
    have hki_K : k < iK.val := htrail.1
    have hkj_K : k < jK.val := htrail.2
    rw [Matrix.stepMatrix_update_eq M k pivot prevPivot iN jN hki_n hkj_n]
    rw [Matrix.stepMatrix_update_eq (Matrix.leadingPrefix M K hK) k pivot prevPivot
      iK jK hki_K hkj_K]
    simp only [Matrix.leadingPrefix_entry]
    rfl
  · by_cases hbelow : k < i ∧ j = k
    · have hki_n : k < iN.val := hbelow.1
      have hjk_n : jN.val = k := hbelow.2
      have hki_K : k < iK.val := hbelow.1
      have hjk_K : jK.val = k := hbelow.2
      rw [Matrix.stepMatrix_pivot_col_below M k pivot prevPivot iN jN hki_n hjk_n]
      rw [Matrix.stepMatrix_pivot_col_below (Matrix.leadingPrefix M K hK) k
        pivot prevPivot iK jK hki_K hjk_K]
    · have hnot_n : ¬ (k < iN.val ∧ k < jN.val) := htrail
      have hnot_n' : ¬ (k < iN.val ∧ jN.val = k) := hbelow
      have hnot_K : ¬ (k < iK.val ∧ k < jK.val) := htrail
      have hnot_K' : ¬ (k < iK.val ∧ jK.val = k) := hbelow
      rw [Matrix.stepMatrix_eq_of_not_update M k pivot prevPivot iN jN hnot_n hnot_n']
      rw [Matrix.stepMatrix_eq_of_not_update (Matrix.leadingPrefix M K hK) k
        pivot prevPivot iK jK hnot_K hnot_K']
      simp only [Matrix.leadingPrefix_entry]
      rfl

/-- A bordered-minor entry equals the source matrix at the lifted index.
The lifted index for a row/column of the bordered minor is the bordered
"row"/"col" anchor when the bordered-minor coordinate hits the last
position (val = k) and the natural inclusion otherwise. -/
private theorem borderedMinor_entry_eq_source
    {n : Nat} (M : Matrix Int n n) (k : Nat) (hk : k < n) (row col : Fin n)
    (i_bm j_bm : Fin (k + 1)) :
    (Matrix.borderedMinor M k hk row col)[i_bm][j_bm] =
      M[(if h : i_bm.val < k then ⟨i_bm.val, Nat.lt_trans h hk⟩ else row)][
        (if h : j_bm.val < k then ⟨j_bm.val, Nat.lt_trans h hk⟩ else col)] := by
  by_cases hi_lt : i_bm.val < k
  · by_cases hj_lt : j_bm.val < k
    · have h := Matrix.borderedMinor_entry_lt_lt M k hk row col i_bm j_bm hi_lt hj_lt
      simp [hi_lt, hj_lt] at h ⊢
      exact h
    · have hj_eq : j_bm.val = k := by
        have := j_bm.isLt
        omega
      have hjFin : j_bm = Fin.last k := Fin.ext (by simp [hj_eq])
      have h := Matrix.borderedMinor_entry_lt_last M k hk row col i_bm hi_lt
      rw [hjFin]
      simp [hi_lt] at h ⊢
      exact h
  · have hi_eq : i_bm.val = k := by
      have := i_bm.isLt
      omega
    have hiFin : i_bm = Fin.last k := Fin.ext (by simp [hi_eq])
    by_cases hj_lt : j_bm.val < k
    · have h := Matrix.borderedMinor_entry_last_lt M k hk row col j_bm hj_lt
      rw [hiFin]
      simp [hj_lt] at h ⊢
      exact h
    · have hj_eq : j_bm.val = k := by
        have := j_bm.isLt
        omega
      have hjFin : j_bm = Fin.last k := Fin.ext (by simp [hj_eq])
      have h := Matrix.borderedMinor_entry_last_last M k hk row col
      rw [hiFin, hjFin]
      simp at h ⊢
      exact h

/-- Promote a bordered-minor coordinate to its lifted index in `Fin n`. -/
private def liftBorderedIdx {n k : Nat} (hk : k < n) (anchor : Fin n) (x : Fin (k + 1)) :
    Fin n :=
  if h : x.val < k then ⟨x.val, Nat.lt_trans h hk⟩ else anchor

private theorem liftBorderedIdx_val_lt {n k : Nat} (hk : k < n) (anchor : Fin n)
    (x : Fin (k + 1)) (h : x.val < k) :
    liftBorderedIdx hk anchor x = ⟨x.val, Nat.lt_trans h hk⟩ := by
  simp [liftBorderedIdx, h]

private theorem liftBorderedIdx_val_eq_k {n k : Nat} (hk : k < n) (anchor : Fin n)
    (x : Fin (k + 1)) (h : x.val = k) :
    liftBorderedIdx hk anchor x = anchor := by
  have : ¬ x.val < k := fun h' => Nat.lt_irrefl _ (h ▸ h')
  simp [liftBorderedIdx, this]

private theorem liftBorderedIdx_at_kStep {n k : Nat} (hk : k < n) (anchor : Fin n)
    {k_step : Nat} (hkstep : k_step < k) (hkstep_lt_n : k_step < n)
    (hkstep_lt_k1 : k_step < k + 1) :
    liftBorderedIdx hk anchor ⟨k_step, hkstep_lt_k1⟩ = ⟨k_step, hkstep_lt_n⟩ := by
  show (if h : k_step < k then (⟨k_step, Nat.lt_trans h hk⟩ : Fin n) else anchor) =
    ⟨k_step, hkstep_lt_n⟩
  simp [hkstep]

private theorem borderedMinor_entry_eq_lift
    {n : Nat} (M : Matrix Int n n) (k : Nat) (hk : k < n) (row col : Fin n)
    (i_bm j_bm : Fin (k + 1)) :
    (Matrix.borderedMinor M k hk row col)[i_bm][j_bm] =
      M[liftBorderedIdx hk row i_bm][liftBorderedIdx hk col j_bm] := by
  rw [borderedMinor_entry_eq_source M k hk row col i_bm j_bm]
  rfl

/-- One Bareiss update step commutes with taking a bordered minor whose
border row/column indices `row`, `col` lie in the trailing block: the
bordered minor of the updated full matrix equals the result of running
the same step on the bordered minor. The pivot/`prevPivot` scalars are
passed through unchanged. -/
private theorem borderedMinor_stepMatrix_eq
    {n : Nat} (M : Matrix Int n n) (k : Nat) (hk : k < n) (row col : Fin n)
    (hrow : k ≤ row.val) (hcol : k ≤ col.val)
    (k_step : Nat) (hkstep : k_step < k) (pivot prevPivot : Int) :
    Matrix.borderedMinor (Matrix.stepMatrix M k_step pivot prevPivot) k hk row col =
      Matrix.stepMatrix (Matrix.borderedMinor M k hk row col) k_step pivot prevPivot := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let i_bm : Fin (k + 1) := ⟨i, hi⟩
  let j_bm : Fin (k + 1) := ⟨j, hj⟩
  let iN : Fin n := liftBorderedIdx hk row i_bm
  let jN : Fin n := liftBorderedIdx hk col j_bm
  -- Equivalence of "in update zone" between bordered minor and source.
  have hi_iff : k_step < i_bm.val ↔ k_step < iN.val := by
    by_cases hi_lt : i_bm.val < k
    · have : iN = ⟨i_bm.val, Nat.lt_trans hi_lt hk⟩ :=
        liftBorderedIdx_val_lt hk row i_bm hi_lt
      rw [show iN.val = i_bm.val from congrArg Fin.val this]
    · have hi_eq : i_bm.val = k := by have := i_bm.isLt; omega
      have : iN = row := liftBorderedIdx_val_eq_k hk row i_bm hi_eq
      rw [show iN.val = row.val from congrArg Fin.val this, hi_eq]
      constructor
      · intro _; exact Nat.lt_of_lt_of_le hkstep hrow
      · intro _; exact hkstep
  have hj_iff : k_step < j_bm.val ↔ k_step < jN.val := by
    by_cases hj_lt : j_bm.val < k
    · have : jN = ⟨j_bm.val, Nat.lt_trans hj_lt hk⟩ :=
        liftBorderedIdx_val_lt hk col j_bm hj_lt
      rw [show jN.val = j_bm.val from congrArg Fin.val this]
    · have hj_eq : j_bm.val = k := by have := j_bm.isLt; omega
      have : jN = col := liftBorderedIdx_val_eq_k hk col j_bm hj_eq
      rw [show jN.val = col.val from congrArg Fin.val this, hj_eq]
      constructor
      · intro _; exact Nat.lt_of_lt_of_le hkstep hcol
      · intro _; exact hkstep
  have hj_eq_iff : j_bm.val = k_step ↔ jN.val = k_step := by
    by_cases hj_lt : j_bm.val < k
    · have : jN = ⟨j_bm.val, Nat.lt_trans hj_lt hk⟩ :=
        liftBorderedIdx_val_lt hk col j_bm hj_lt
      rw [show jN.val = j_bm.val from congrArg Fin.val this]
    · have hj_eq : j_bm.val = k := by have := j_bm.isLt; omega
      have : jN = col := liftBorderedIdx_val_eq_k hk col j_bm hj_eq
      rw [show jN.val = col.val from congrArg Fin.val this, hj_eq]
      constructor
      · intro h; omega
      · intro h; exact absurd h (Nat.ne_of_gt (Nat.lt_of_lt_of_le hkstep hcol))
  -- Identify: borderedMinor entry at (i_bm, j_bm) equals M entry at (iN, jN).
  have h_entry : ∀ (M' : Matrix Int n n) (r : Fin (k + 1)) (c : Fin (k + 1)),
      (Matrix.borderedMinor M' k hk row col)[r][c] =
        M'[liftBorderedIdx hk row r][liftBorderedIdx hk col c] :=
    fun M' r c => borderedMinor_entry_eq_lift M' k hk row col r c
  show (Matrix.borderedMinor (Matrix.stepMatrix M k_step pivot prevPivot) k hk row col)[i_bm][j_bm] =
       (Matrix.stepMatrix (Matrix.borderedMinor M k hk row col) k_step pivot prevPivot)[i_bm][j_bm]
  rw [h_entry (Matrix.stepMatrix M k_step pivot prevPivot) i_bm j_bm]
  -- LHS = (stepMatrix M k_step pivot prevPivot)[iN][jN].
  by_cases htrail_bm : k_step < i_bm.val ∧ k_step < j_bm.val
  · have htrail_N : k_step < iN.val ∧ k_step < jN.val :=
      ⟨hi_iff.mp htrail_bm.1, hj_iff.mp htrail_bm.2⟩
    -- Pivot column / pivot row indices in `Fin (k+1)` have val = k_step < k.
    have hkstep_lt_k1 : k_step < k + 1 := Nat.lt_succ_of_lt hkstep
    have hkstep_lt_n : k_step < n := Nat.lt_trans hkstep hk
    let colK_bm : Fin (k + 1) := ⟨k_step, hkstep_lt_k1⟩
    let colK_N : Fin n := ⟨k_step, hkstep_lt_n⟩
    have hcolK_row : liftBorderedIdx hk row colK_bm = colK_N :=
      liftBorderedIdx_at_kStep hk row hkstep hkstep_lt_n hkstep_lt_k1
    have hcolK_col : liftBorderedIdx hk col colK_bm = colK_N :=
      liftBorderedIdx_at_kStep hk col hkstep hkstep_lt_n hkstep_lt_k1
    have h_iK : (Matrix.borderedMinor M k hk row col)[i_bm][colK_bm] = M[iN][colK_N] := by
      rw [h_entry M i_bm colK_bm]
      show M[iN][liftBorderedIdx hk col colK_bm] = M[iN][colK_N]
      exact congrArg (fun (x : Fin n) => M[iN][x]) hcolK_col
    have h_Kj : (Matrix.borderedMinor M k hk row col)[colK_bm][j_bm] = M[colK_N][jN] := by
      rw [h_entry M colK_bm j_bm]
      show M[liftBorderedIdx hk row colK_bm][jN] = M[colK_N][jN]
      exact congrArg (fun (x : Fin n) => M[x][jN]) hcolK_row
    -- Compute LHS directly.
    have hLHS :
        (Matrix.stepMatrix M k_step pivot prevPivot)[iN][jN] =
          Matrix.exactDiv (pivot * M[iN][jN] -
            M[iN][colK_N] * M[colK_N][jN]) prevPivot := by
      rw [Matrix.stepMatrix_update_eq M k_step pivot prevPivot iN jN htrail_N.1 htrail_N.2]
    have hRHS :
        (Matrix.stepMatrix (Matrix.borderedMinor M k hk row col) k_step pivot prevPivot)[i_bm][j_bm] =
          Matrix.exactDiv (pivot * (Matrix.borderedMinor M k hk row col)[i_bm][j_bm] -
            (Matrix.borderedMinor M k hk row col)[i_bm][colK_bm] *
            (Matrix.borderedMinor M k hk row col)[colK_bm][j_bm]) prevPivot := by
      rw [Matrix.stepMatrix_update_eq (Matrix.borderedMinor M k hk row col) k_step pivot prevPivot
        i_bm j_bm htrail_bm.1 htrail_bm.2]
    rw [hLHS, hRHS, h_entry M i_bm j_bm, h_iK, h_Kj]
  · by_cases hbelow_bm : k_step < i_bm.val ∧ j_bm.val = k_step
    · have hi_N : k_step < iN.val := hi_iff.mp hbelow_bm.1
      have hj_N : jN.val = k_step := hj_eq_iff.mp hbelow_bm.2
      rw [Matrix.stepMatrix_pivot_col_below M k_step pivot prevPivot iN jN hi_N hj_N]
      rw [Matrix.stepMatrix_pivot_col_below (Matrix.borderedMinor M k hk row col) k_step
        pivot prevPivot i_bm j_bm hbelow_bm.1 hbelow_bm.2]
    · -- Outside the update zone on both sides.
      have hnot_trail_N : ¬ (k_step < iN.val ∧ k_step < jN.val) := by
        intro h
        exact htrail_bm ⟨hi_iff.mpr h.1, hj_iff.mpr h.2⟩
      have hnot_below_N : ¬ (k_step < iN.val ∧ jN.val = k_step) := by
        intro h
        exact hbelow_bm ⟨hi_iff.mpr h.1, hj_eq_iff.mpr h.2⟩
      rw [Matrix.stepMatrix_eq_of_not_update M k_step pivot prevPivot iN jN
        hnot_trail_N hnot_below_N]
      rw [Matrix.stepMatrix_eq_of_not_update (Matrix.borderedMinor M k hk row col) k_step
        pivot prevPivot i_bm j_bm htrail_bm hbelow_bm]
      exact (h_entry M i_bm j_bm).symm

/-- Run `noPivotLoop` on a full `n × n` matrix and on its `(k + 1) × (k + 1)`
bordered minor (whose border row/column indices `row`, `col` lie in the
trailing block) from two BareissStates that agree under the bordered
minor. While both runs are still synchronized (`fuel + state.step < k + 1`),
their bookkeeping fields agree and the full state's matrix, restricted
to the bordered minor, matches the bordered-minor state's matrix. -/
private theorem noPivotLoop_sync_borderedMinor_aux
    {n : Nat} (k : Nat) (hk : k < n) (row col : Fin n)
    (hrow : k ≤ row.val) (hcol : k ≤ col.val) (fuel : Nat) :
    ∀ (state_full : Matrix.BareissState n) (state_bm : Matrix.BareissState (k + 1)),
      state_full.step = state_bm.step →
      state_full.prevPivot = state_bm.prevPivot →
      state_full.rowSwaps = state_bm.rowSwaps →
      state_full.singularStep = state_bm.singularStep →
      Matrix.borderedMinor state_full.matrix k hk row col = state_bm.matrix →
      fuel + state_full.step < k + 1 →
      (Matrix.noPivotLoop fuel state_full).step =
          (Matrix.noPivotLoop fuel state_bm).step ∧
      (Matrix.noPivotLoop fuel state_full).prevPivot =
          (Matrix.noPivotLoop fuel state_bm).prevPivot ∧
      (Matrix.noPivotLoop fuel state_full).rowSwaps =
          (Matrix.noPivotLoop fuel state_bm).rowSwaps ∧
      (Matrix.noPivotLoop fuel state_full).singularStep =
          (Matrix.noPivotLoop fuel state_bm).singularStep ∧
      Matrix.borderedMinor (Matrix.noPivotLoop fuel state_full).matrix k hk row col =
          (Matrix.noPivotLoop fuel state_bm).matrix := by
  induction fuel with
  | zero =>
      intros state_full state_bm h_step h_prev h_rows h_sing h_mat _hfuel
      simp only [Matrix.noPivotLoop]
      exact ⟨h_step, h_prev, h_rows, h_sing, h_mat⟩
  | succ f ih =>
      intros state_full state_bm h_step h_prev h_rows h_sing h_mat hfuel
      have h_step_lt_k1 : state_full.step + 1 < k + 1 := by omega
      have h_step_lt_k : state_full.step < k := by omega
      have h_step_lt_n : state_full.step < n := Nat.lt_trans h_step_lt_k hk
      have h_full_done : state_full.step + 1 < n := by
        have hk_le : k + 1 ≤ n := Nat.succ_le_of_lt hk
        omega
      have h_bm_done : state_bm.step + 1 < k + 1 := h_step ▸ h_step_lt_k1
      have h_bm_step_lt_k : state_bm.step < k := h_step ▸ h_step_lt_k
      let k_full : Fin n := ⟨state_full.step, h_step_lt_n⟩
      let k_bm : Fin (k + 1) := ⟨state_bm.step, Nat.lt_succ_of_lt h_bm_step_lt_k⟩
      have h_k_bm_lt : k_bm.val < k := h_bm_step_lt_k
      -- Pivot entries agree because borderedMinor of full state's matrix equals bm state's matrix.
      have h_pivot_eq :
          state_full.matrix[k_full][k_full] = state_bm.matrix[k_bm][k_bm] := by
        have hcongr :
            (Matrix.borderedMinor state_full.matrix k hk row col)[k_bm][k_bm] =
              state_bm.matrix[k_bm][k_bm] := by rw [h_mat]
        have h_bm_entry :=
          Matrix.borderedMinor_entry_lt_lt state_full.matrix k hk row col k_bm k_bm
            h_k_bm_lt h_k_bm_lt
        simp only at h_bm_entry
        rw [h_bm_entry] at hcongr
        have h_idx : k_full = (⟨k_bm.val, Nat.lt_trans h_k_bm_lt hk⟩ : Fin n) :=
          Fin.ext h_step
        calc state_full.matrix[k_full][k_full]
            = state_full.matrix[(⟨k_bm.val, Nat.lt_trans h_k_bm_lt hk⟩ : Fin n)][
                (⟨k_bm.val, Nat.lt_trans h_k_bm_lt hk⟩ : Fin n)] :=
              congrArg (fun (i : Fin n) => state_full.matrix[i][i]) h_idx
          _ = state_bm.matrix[k_bm][k_bm] := hcongr
      by_cases hp_full : state_full.matrix[k_full][k_full] = 0
      · -- Singular branch on both sides.
        have hp_bm : state_bm.matrix[k_bm][k_bm] = 0 := by
          rw [← h_pivot_eq]; exact hp_full
        rw [Matrix.noPivotLoop_singular_branch f state_full h_full_done hp_full]
        rw [Matrix.noPivotLoop_singular_branch f state_bm h_bm_done hp_bm]
        refine ⟨h_step, h_prev, h_rows, ?_, h_mat⟩
        simp [h_step]
      · -- Regular branch on both sides; apply IH to the updated states.
        have hp_bm : state_bm.matrix[k_bm][k_bm] ≠ 0 := by
          rw [← h_pivot_eq]; exact hp_full
        rw [Matrix.noPivotLoop_regular_branch f state_full h_full_done hp_full]
        rw [Matrix.noPivotLoop_regular_branch f state_bm h_bm_done hp_bm]
        have h_new_mat :
            Matrix.borderedMinor
              (Matrix.stepMatrix state_full.matrix state_full.step
                state_full.matrix[k_full][k_full] state_full.prevPivot) k hk row col =
              Matrix.stepMatrix state_bm.matrix state_bm.step
                state_bm.matrix[k_bm][k_bm] state_bm.prevPivot := by
          rw [borderedMinor_stepMatrix_eq state_full.matrix k hk row col hrow hcol
              state_full.step h_step_lt_k state_full.matrix[k_full][k_full]
              state_full.prevPivot, h_mat, h_step, h_prev, h_pivot_eq]
        apply ih
        · -- step
          simp [h_step]
        · -- prevPivot
          exact h_pivot_eq
        · -- rowSwaps
          exact h_rows
        · -- singularStep
          rfl
        · -- matrix
          exact h_new_mat
        · -- fuel
          simp; omega

/-- The `(row, col)` entry of the noPivot Bareiss state after `k` iterations on
the full `n × n` matrix agrees with the `(Fin.last k, Fin.last k)` entry of the
noPivot Bareiss state after `k` iterations on the `(k + 1) × (k + 1)` bordered
minor at `row, col`. The `singularStep` bookkeeping also agrees, mirroring the
leading-prefix sync corollary. Requires `row, col` to lie in the trailing block. -/
theorem noPivotLoop_full_eq_borderedMinor_at_trailing
    {n : Nat} (M : Matrix Int n n) (k : Nat) (hk : k < n) (row col : Fin n)
    (hrow : k ≤ row.val) (hcol : k ≤ col.val) :
    let BM := Matrix.borderedMinor M k hk row col
    let s_full := Matrix.noPivotLoop k (Matrix.noPivotInitialState M)
    let s_bm := Matrix.noPivotLoop k (Matrix.noPivotInitialState BM)
    s_full.matrix[row][col] = s_bm.matrix[Fin.last k][Fin.last k] ∧
      s_full.singularStep = s_bm.singularStep := by
  intro BM s_full s_bm
  have h_sync :=
    noPivotLoop_sync_borderedMinor_aux k hk row col hrow hcol k
      (Matrix.noPivotInitialState M) (Matrix.noPivotInitialState BM)
      rfl rfl rfl rfl rfl
      (show k + (Matrix.noPivotInitialState M).step < k + 1 by
        simp [Matrix.noPivotInitialState])
  obtain ⟨_, _, _, h_sing, h_mat⟩ := h_sync
  refine ⟨?_, h_sing⟩
  -- The (row, col) entry of s_full.matrix is the (Fin.last k, Fin.last k) entry of
  -- (borderedMinor s_full.matrix k hk row col), which equals s_bm.matrix by `h_mat`.
  have hcongr :
      (Matrix.borderedMinor s_full.matrix k hk row col)[Fin.last k][Fin.last k] =
        s_bm.matrix[Fin.last k][Fin.last k] := by rw [h_mat]
  rw [Matrix.borderedMinor_entry_last_last] at hcongr
  exact hcongr

/-- The step field of a no-pivot Bareiss state advances by at most `fuel` after
`fuel` loop iterations. Combined with `noPivotLoop_step_monotone`, this brackets
the resulting step between the starting step and the starting step plus the
fuel. -/
private theorem noPivotLoop_step_le_add
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState n) :
    (Matrix.noPivotLoop fuel state).step ≤ state.step + fuel := by
  induction fuel generalizing state with
  | zero =>
      show state.step ≤ state.step + 0
      omega
  | succ f ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · rw [Matrix.noPivotLoop_singular_branch f state hDone hp]
          show state.step ≤ state.step + (f + 1)
          omega
        · rw [Matrix.noPivotLoop_regular_branch f state hDone hp]
          calc (Matrix.noPivotLoop f
              { step := state.step + 1
                matrix := Matrix.stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot
                prevPivot := state.matrix[state.step][state.step]
                rowSwaps := state.rowSwaps
                singularStep := none }).step
              ≤ state.step + 1 + f := ih _
            _ = state.step + (f + 1) := by omega
      · rw [Matrix.noPivotLoop_done f state hDone]
        show state.step ≤ state.step + (f + 1)
        omega

/-- Trailing-block symmetry is preserved by the no-pivot Bareiss loop: if the
input state's matrix is symmetric at indices at or beyond `state.step`, then the
resulting state's matrix is symmetric at indices at or beyond its `step`. The
abstract version takes only the input symmetry hypothesis; the diagonal Bareiss
update commutes through symmetry because the trailing block remains symmetric
after each `stepMatrix` application. -/
private theorem noPivotLoop_matrix_symm_preserve
    {n : Nat} (fuel : Nat) :
    ∀ (state : Matrix.BareissState n),
      (∀ a b : Fin n, state.step ≤ a.val → state.step ≤ b.val →
        state.matrix[a][b] = state.matrix[b][a]) →
      ∀ (a b : Fin n),
        (Matrix.noPivotLoop fuel state).step ≤ a.val →
        (Matrix.noPivotLoop fuel state).step ≤ b.val →
        (Matrix.noPivotLoop fuel state).matrix[a][b] =
          (Matrix.noPivotLoop fuel state).matrix[b][a] := by
  induction fuel with
  | zero =>
      intros state h_sym a b ha hb
      change state.matrix[a][b] = state.matrix[b][a]
      change state.step ≤ a.val at ha
      change state.step ≤ b.val at hb
      exact h_sym a b ha hb
  | succ f ih =>
      intros state h_sym a b ha hb
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · -- Singular branch: result is `{state with singularStep := some state.step}`.
          rw [Matrix.noPivotLoop_singular_branch f state hDone hp] at ha hb ⊢
          change state.matrix[a][b] = state.matrix[b][a]
          change state.step ≤ a.val at ha
          change state.step ≤ b.val at hb
          exact h_sym a b ha hb
        · -- Regular branch: recurse on the updated state with step + 1.
          rw [Matrix.noPivotLoop_regular_branch f state hDone hp] at ha hb ⊢
          let kFin : Fin n := ⟨state.step, Nat.lt_of_succ_lt hDone⟩
          have h_sym_new : ∀ (a' b' : Fin n),
              state.step + 1 ≤ a'.val → state.step + 1 ≤ b'.val →
              (Matrix.stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot)[a'][b']
                = (Matrix.stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot)[b'][a'] := by
            intros a' b' ha' hb'
            have ha'_lt : state.step < a'.val := ha'
            have hb'_lt : state.step < b'.val := hb'
            rw [Matrix.stepMatrix_update_eq state.matrix state.step
              state.matrix[state.step][state.step] state.prevPivot a' b' ha'_lt hb'_lt]
            rw [Matrix.stepMatrix_update_eq state.matrix state.step
              state.matrix[state.step][state.step] state.prevPivot b' a' hb'_lt ha'_lt]
            -- Both sides reduce to `exactDiv` of similar expressions. Identify
            -- the two `Fin n` indices at value `state.step` and use the
            -- trailing-block symmetry of `state.matrix`.
            have h_ab : state.matrix[a'][b'] = state.matrix[b'][a'] :=
              h_sym a' b' (Nat.le_of_lt ha'_lt) (Nat.le_of_lt hb'_lt)
            have h_ak : state.matrix[a'][kFin] = state.matrix[kFin][a'] :=
              h_sym a' kFin (Nat.le_of_lt ha'_lt) (Nat.le_refl _)
            have h_bk : state.matrix[b'][kFin] = state.matrix[kFin][b'] :=
              h_sym b' kFin (Nat.le_of_lt hb'_lt) (Nat.le_refl _)
            -- The two `Fin n` indices in the unfolded `stepMatrix_update_eq`
            -- have value `state.step` and so equal `kFin` definitionally.
            change Matrix.exactDiv (_ * state.matrix[a'][b']
                - state.matrix[a'][kFin] * state.matrix[kFin][b']) _
              = Matrix.exactDiv (_ * state.matrix[b'][a']
                - state.matrix[b'][kFin] * state.matrix[kFin][a']) _
            rw [h_ab, h_ak, h_bk]
            congr 1
            grind
          exact ih
            { step := state.step + 1
              matrix := Matrix.stepMatrix state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot
              prevPivot := state.matrix[state.step][state.step]
              rowSwaps := state.rowSwaps
              singularStep := none }
            (by
              intros a' b' ha' hb'
              exact h_sym_new a' b' ha' hb')
            a b ha hb
      · -- Boundary case: `noPivotLoop` returns the input state unchanged.
        rw [Matrix.noPivotLoop_done f state hDone] at ha hb ⊢
        change state.matrix[a][b] = state.matrix[b][a]
        change state.step ≤ a.val at ha
        change state.step ≤ b.val at hb
        exact h_sym a b ha hb

/-- Identification of Bareiss-style trailing values across two bordered minors
of a symmetric matrix obtained by swapping the border row and column. Composed from
`noPivotLoop_full_eq_borderedMinor_at_trailing` (applied at both swapped
positions) and `noPivotLoop_matrix_symm_preserve` (which transports the
trailing-block symmetry of the input through the loop). -/
private theorem noPivotLoop_borderedMinor_swap_at_trailing
    {n : Nat} (M : Matrix Int n n)
    (h_sym : ∀ a b : Fin n, M[a][b] = M[b][a])
    (k : Nat) (hk : k < n) (i j : Fin n)
    (hki : k ≤ i.val) (hkj : k ≤ j.val) :
    (Matrix.noPivotLoop k (Matrix.noPivotInitialState
        (Matrix.borderedMinor M k hk i j))).matrix[Fin.last k][Fin.last k] =
    (Matrix.noPivotLoop k (Matrix.noPivotInitialState
        (Matrix.borderedMinor M k hk j i))).matrix[Fin.last k][Fin.last k] := by
  -- Reduce both sides through the full-matrix sync at swapped border positions.
  have h_ij :=
    (noPivotLoop_full_eq_borderedMinor_at_trailing M k hk i j hki hkj).1
  have h_ji :=
    (noPivotLoop_full_eq_borderedMinor_at_trailing M k hk j i hkj hki).1
  rw [← h_ij, ← h_ji]
  -- Reduce to symmetry of the full-matrix noPivotLoop at `(i, j)` vs `(j, i)`.
  -- Both indices are bounded below by `k`, and the loop's resulting step is at
  -- most `0 + k = k`, hence at most each of `i.val`, `j.val`.
  have h_step_le := noPivotLoop_step_le_add k (Matrix.noPivotInitialState M)
  have h_step0 : (Matrix.noPivotInitialState M).step = 0 := rfl
  have h_step_bound :
      (Matrix.noPivotLoop k (Matrix.noPivotInitialState M)).step ≤ k := by
    rw [h_step0] at h_step_le
    simpa using h_step_le
  have h_init_sym :
      ∀ a b : Fin n, (Matrix.noPivotInitialState M).step ≤ a.val →
        (Matrix.noPivotInitialState M).step ≤ b.val →
        (Matrix.noPivotInitialState M).matrix[a][b] =
          (Matrix.noPivotInitialState M).matrix[b][a] := by
    intros a b _ _
    exact h_sym a b
  exact noPivotLoop_matrix_symm_preserve k
    (Matrix.noPivotInitialState M) h_init_sym i j
    (Nat.le_trans h_step_bound hki) (Nat.le_trans h_step_bound hkj)

/-- Run `noPivotLoop` on a full `n × n` matrix and on its `K × K` leading
prefix from two BareissStates that agree on the leading prefix. While
both runs are still synchronized (fuel fits within `K - state.step`),
their bookkeeping fields agree and the full state's matrix, restricted
to the leading prefix, matches the prefix state's matrix. -/
private theorem noPivotLoop_sync_leadingPrefix_aux
    {n K : Nat} (hK : K ≤ n) (fuel : Nat) :
    ∀ (state_full : Matrix.BareissState n) (state_pref : Matrix.BareissState K),
      state_full.step = state_pref.step →
      state_full.prevPivot = state_pref.prevPivot →
      state_full.rowSwaps = state_pref.rowSwaps →
      state_full.singularStep = state_pref.singularStep →
      Matrix.leadingPrefix state_full.matrix K hK = state_pref.matrix →
      fuel + state_full.step < K →
      (Matrix.noPivotLoop fuel state_full).step =
          (Matrix.noPivotLoop fuel state_pref).step ∧
      (Matrix.noPivotLoop fuel state_full).prevPivot =
          (Matrix.noPivotLoop fuel state_pref).prevPivot ∧
      (Matrix.noPivotLoop fuel state_full).rowSwaps =
          (Matrix.noPivotLoop fuel state_pref).rowSwaps ∧
      (Matrix.noPivotLoop fuel state_full).singularStep =
          (Matrix.noPivotLoop fuel state_pref).singularStep ∧
      Matrix.leadingPrefix (Matrix.noPivotLoop fuel state_full).matrix K hK =
          (Matrix.noPivotLoop fuel state_pref).matrix := by
  induction fuel with
  | zero =>
      intros state_full state_pref h_step h_prev h_rows h_sing h_mat _hfuel
      simp only [Matrix.noPivotLoop]
      exact ⟨h_step, h_prev, h_rows, h_sing, h_mat⟩
  | succ f ih =>
      intros state_full state_pref h_step h_prev h_rows h_sing h_mat hfuel
      have h_step_lt_K : state_full.step + 1 < K := by omega
      have h_full_done : state_full.step + 1 < n :=
        Nat.lt_of_lt_of_le h_step_lt_K hK
      have h_pref_done : state_pref.step + 1 < K := h_step ▸ h_step_lt_K
      have h_step_lt_n : state_full.step < n := Nat.lt_of_succ_lt h_full_done
      have h_step_lt_K_strict : state_full.step < K :=
        Nat.lt_of_succ_lt h_step_lt_K
      have h_pref_step_lt_K : state_pref.step < K := h_step ▸ h_step_lt_K_strict
      let k_full : Fin n := ⟨state_full.step, h_step_lt_n⟩
      let k_pref : Fin K := ⟨state_pref.step, h_pref_step_lt_K⟩
      let k_full' : Fin K := ⟨state_full.step, h_step_lt_K_strict⟩
      -- The pivot entries agree on both sides because the full state's
      -- matrix, restricted to the leading prefix, equals the prefix state's
      -- matrix.
      have h_k_eq : k_full' = k_pref := Fin.ext h_step
      have h_pivot_eq : state_full.matrix[k_full][k_full] =
          state_pref.matrix[k_pref][k_pref] := by
        have hcongr := congrArg (fun (M : Matrix Int K K) => M[k_pref][k_pref]) h_mat
        simp only [Matrix.leadingPrefix_entry] at hcongr
        -- hcongr : state_full.matrix[⟨k_pref.val, _⟩][⟨k_pref.val, _⟩] =
        --          state_pref.matrix[k_pref][k_pref]
        -- k_full.val = state_full.step = state_pref.step = k_pref.val (by h_step),
        -- so as Fin n elements they coincide. Use congrArg on the diagonal
        -- entry as a function of Fin n to close the gap.
        have h_idx :
            k_full = (⟨k_pref.val, Nat.lt_of_lt_of_le k_pref.isLt hK⟩ : Fin n) :=
          Fin.ext h_step
        have h_diag :
            state_full.matrix[k_full][k_full] =
              state_full.matrix[(⟨k_pref.val, Nat.lt_of_lt_of_le k_pref.isLt hK⟩ : Fin n)][(⟨k_pref.val, Nat.lt_of_lt_of_le k_pref.isLt hK⟩ : Fin n)] :=
          congrArg (fun (i : Fin n) => state_full.matrix[i][i]) h_idx
        exact h_diag.trans hcongr
      by_cases hp_full : state_full.matrix[k_full][k_full] = 0
      · -- Singular branch on both sides.
        have hp_pref : state_pref.matrix[k_pref][k_pref] = 0 := by
          rw [← h_pivot_eq]; exact hp_full
        rw [Matrix.noPivotLoop_singular_branch f state_full h_full_done hp_full]
        rw [Matrix.noPivotLoop_singular_branch f state_pref h_pref_done hp_pref]
        refine ⟨h_step, h_prev, h_rows, ?_, h_mat⟩
        simp [h_step]
      · -- Regular branch on both sides; apply IH to the updated states.
        have hp_pref : state_pref.matrix[k_pref][k_pref] ≠ 0 := by
          rw [← h_pivot_eq]; exact hp_full
        rw [Matrix.noPivotLoop_regular_branch f state_full h_full_done hp_full]
        rw [Matrix.noPivotLoop_regular_branch f state_pref h_pref_done hp_pref]
        -- After one step, the new states are still linked.
        have h_new_mat :
            Matrix.leadingPrefix
              (Matrix.stepMatrix state_full.matrix state_full.step
                state_full.matrix[k_full][k_full] state_full.prevPivot) K hK =
              Matrix.stepMatrix state_pref.matrix state_pref.step
                state_pref.matrix[k_pref][k_pref] state_pref.prevPivot := by
          rw [leadingPrefix_stepMatrix_eq, h_mat, h_step, h_prev, h_pivot_eq]
        apply ih
        · -- step
          simp [h_step]
        · -- prevPivot
          exact h_pivot_eq
        · -- rowSwaps
          exact h_rows
        · -- singularStep
          rfl
        · -- matrix
          exact h_new_mat
        · -- fuel
          simp; omega

/-- Once the no-pivot Bareiss loop has reached the boundary
(`state.step + 1 ≥ n`), any further fuel is a no-op. -/
private theorem noPivotLoop_id_at_done
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState n)
    (hDone : ¬ state.step + 1 < n) :
    Matrix.noPivotLoop fuel state = state := by
  induction fuel with
  | zero => rfl
  | succ f _ih => exact Matrix.noPivotLoop_done f state hDone

/-- Once the no-pivot Bareiss loop has marked the current step singular
(`state.singularStep = some state.step` with a zero pivot at that step),
any further fuel is a no-op. -/
theorem noPivotLoop_id_at_singular_fixedpoint
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[(⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][(⟨state.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0)
    (hsing : state.singularStep = some state.step) :
    Matrix.noPivotLoop fuel state = state := by
  induction fuel with
  | zero => rfl
  | succ f _ih =>
      rw [Matrix.noPivotLoop_singular_branch f state hDone hp]
      -- Goal: {state with singularStep := some state.step} = state.
      cases state with
      | mk step matrix prevPivot rowSwaps singularStep =>
        simp only at hsing
        subst hsing
        rfl

/-- Fuel composition for the no-pivot Bareiss loop: running `a + b` units of
fuel from `state` equals running `b` more units after `a` initial units. -/
theorem noPivotLoop_add
    {n : Nat} (a b : Nat) (state : Matrix.BareissState n) :
    Matrix.noPivotLoop (a + b) state =
      Matrix.noPivotLoop b (Matrix.noPivotLoop a state) := by
  induction a generalizing state with
  | zero =>
      show Matrix.noPivotLoop (0 + b) state = Matrix.noPivotLoop b state
      simp
  | succ a' ih =>
      by_cases hDone : state.step + 1 < n
      · let k : Fin n :=
          ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        by_cases hp : state.matrix[k][k] = 0
        · -- Singular: both sides collapse to `{state with singularStep := some state.step}`.
          have h_lhs :
              Matrix.noPivotLoop (a' + 1 + b) state =
                {state with singularStep := some state.step} := by
            have : a' + 1 + b = (a' + b) + 1 := by omega
            rw [this]
            exact Matrix.noPivotLoop_singular_branch (a' + b) state hDone hp
          have h_rhs_inner :
              Matrix.noPivotLoop (a' + 1) state =
                {state with singularStep := some state.step} :=
            Matrix.noPivotLoop_singular_branch a' state hDone hp
          rw [h_lhs, h_rhs_inner]
          symm
          -- Now show: noPivotLoop b {state with singularStep := some state.step} = that.
          let s' : Matrix.BareissState n :=
            {state with singularStep := some state.step}
          have hDone_s' : s'.step + 1 < n := hDone
          have hp_s' : s'.matrix[(⟨s'.step, Nat.lt_of_succ_lt hDone_s'⟩ : Fin n)][(⟨s'.step, Nat.lt_of_succ_lt hDone_s'⟩ : Fin n)] = 0 := hp
          have hsing_s' : s'.singularStep = some s'.step := rfl
          exact noPivotLoop_id_at_singular_fixedpoint b s' hDone_s' hp_s' hsing_s'
        · -- Regular: both sides do one step then recurse on `next`.
          have h_lhs :
              Matrix.noPivotLoop (a' + 1 + b) state =
                Matrix.noPivotLoop (a' + b)
                  { step := state.step + 1
                    matrix := Matrix.stepMatrix state.matrix state.step
                      state.matrix[k][k] state.prevPivot
                    prevPivot := state.matrix[k][k]
                    rowSwaps := state.rowSwaps
                    singularStep := none } := by
            have : a' + 1 + b = (a' + b) + 1 := by omega
            rw [this]
            exact Matrix.noPivotLoop_regular_branch (a' + b) state hDone hp
          have h_rhs_inner :
              Matrix.noPivotLoop (a' + 1) state =
                Matrix.noPivotLoop a'
                  { step := state.step + 1
                    matrix := Matrix.stepMatrix state.matrix state.step
                      state.matrix[k][k] state.prevPivot
                    prevPivot := state.matrix[k][k]
                    rowSwaps := state.rowSwaps
                    singularStep := none } :=
            Matrix.noPivotLoop_regular_branch a' state hDone hp
          rw [h_lhs, h_rhs_inner]
          exact ih _
      · -- Boundary: both sides return `state` unchanged.
        rw [noPivotLoop_id_at_done (a' + 1 + b) state hDone]
        rw [noPivotLoop_id_at_done (a' + 1) state hDone]
        exact (noPivotLoop_id_at_done b state hDone).symm

/-- After running `noPivotLoop` from a state without a recorded singular
step, the result has either no singular step, or it has a singular step
that matches the current `step` field together with a zero pivot at that
position. -/
theorem noPivotLoop_singular_inv
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState n)
    (h_init : state.singularStep = none) :
    (Matrix.noPivotLoop fuel state).singularStep = none ∨
    ∃ k : Fin n,
      (Matrix.noPivotLoop fuel state).singularStep = some k.val ∧
      (Matrix.noPivotLoop fuel state).step = k.val ∧
      (Matrix.noPivotLoop fuel state).matrix[k][k] = 0 ∧
      k.val + 1 < n := by
  induction fuel generalizing state with
  | zero =>
      left
      change state.singularStep = none
      exact h_init
  | succ f ih =>
      by_cases hDone : state.step + 1 < n
      · let k : Fin n := ⟨state.step, Nat.lt_of_succ_lt hDone⟩
        by_cases hp : state.matrix[k][k] = 0
        · -- Singular branch: result = {state with singularStep := some state.step}.
          right
          refine ⟨k, ?_, ?_, ?_, hDone⟩
          · rw [Matrix.noPivotLoop_singular_branch f state hDone hp]
          · rw [Matrix.noPivotLoop_singular_branch f state hDone hp]
          · rw [Matrix.noPivotLoop_singular_branch f state hDone hp]
            exact hp
        · -- Regular branch
          rw [Matrix.noPivotLoop_regular_branch f state hDone hp]
          exact ih _ rfl
      · -- Boundary
        rw [Matrix.noPivotLoop_done f state hDone]
        left; exact h_init

/-- When the no-pivot Bareiss loop starts from a non-singular state and records
a singular step within `fuel` iterations, the recorded singular index is
strictly bounded by the initial step plus the fuel. The singular branch sets
`singularStep := some state.step` at the trigger iteration, and `state.step`
advances by at most one per regular iteration; with `fuel` iterations available
and at least one used for the singular trigger, the recorded index is `< start
+ fuel`. -/
theorem noPivotLoop_singularStep_lt
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState n)
    (h_init : state.singularStep = none)
    (s : Nat)
    (h_sing : (Matrix.noPivotLoop fuel state).singularStep = some s) :
    s < state.step + fuel := by
  induction fuel generalizing state with
  | zero =>
      rw [Matrix.noPivotLoop_zero_fuel, h_init] at h_sing
      nomatch h_sing
  | succ f ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · rw [Matrix.noPivotLoop_singular_branch f state hDone hp] at h_sing
          simp at h_sing
          omega
        · rw [Matrix.noPivotLoop_regular_branch f state hDone hp] at h_sing
          have h_ih := ih
            { step := state.step + 1
              matrix := Matrix.stepMatrix state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot
              prevPivot := state.matrix[state.step][state.step]
              rowSwaps := state.rowSwaps
              singularStep := none }
            rfl h_sing
          change s < state.step + 1 + f at h_ih
          show s < state.step + (f + 1)
          omega
      · rw [Matrix.noPivotLoop_done f state hDone] at h_sing
        rw [h_init] at h_sing
        nomatch h_sing

/-- After running `fuel` iterations of `Matrix.noPivotLoop` from a state with
no recorded singular step, if the result also has no recorded singular step
and the loop had at least `fuel + 1` steps of room from its starting step,
then the result's step is the starting step plus `fuel`. -/
private theorem noPivotLoop_step_eq_add_of_singularStep_none
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState n)
    (h_init : state.singularStep = none)
    (h_room : state.step + fuel + 1 ≤ n)
    (h_no_sing : (Matrix.noPivotLoop fuel state).singularStep = none) :
    (Matrix.noPivotLoop fuel state).step = state.step + fuel := by
  induction fuel generalizing state with
  | zero =>
      show state.step = state.step + 0
      omega
  | succ f ih =>
      have hDone : state.step + 1 < n := by omega
      by_cases hp : state.matrix[state.step][state.step] = 0
      · rw [Matrix.noPivotLoop_singular_branch f state hDone hp] at h_no_sing
        simp at h_no_sing
      · rw [Matrix.noPivotLoop_regular_branch f state hDone hp] at h_no_sing
        rw [Matrix.noPivotLoop_regular_branch f state hDone hp]
        have h_next_room : state.step + 1 + f + 1 ≤ n := by omega
        have h_next_step := ih
          { step := state.step + 1
            matrix := Matrix.stepMatrix state.matrix state.step
              state.matrix[state.step][state.step] state.prevPivot
            prevPivot := state.matrix[state.step][state.step]
            rowSwaps := state.rowSwaps
            singularStep := none }
          rfl h_next_room h_no_sing
        rw [h_next_step]
        show state.step + 1 + f = state.step + (f + 1)
        omega

/-- A no-pivot Bareiss pass that never records a singular step preserves the
nonzero status of the previous pivot. Regular branches replace `prevPivot` by
the current nonzero pivot; singular branches contradict the final
`singularStep = none` hypothesis. -/
private theorem noPivotLoop_prevPivot_ne_zero_of_singularStep_none
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState n)
    (hprev : state.prevPivot ≠ 0)
    (h_no_sing : (Matrix.noPivotLoop fuel state).singularStep = none) :
    (Matrix.noPivotLoop fuel state).prevPivot ≠ 0 := by
  induction fuel generalizing state with
  | zero =>
      simpa [Matrix.noPivotLoop_zero_fuel] using hprev
  | succ f ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · rw [Matrix.noPivotLoop_singular_branch f state hDone hp] at h_no_sing
          simp at h_no_sing
        · rw [Matrix.noPivotLoop_regular_branch f state hDone hp] at h_no_sing
          rw [Matrix.noPivotLoop_regular_branch f state hDone hp]
          exact ih
            { step := state.step + 1
              matrix := Matrix.stepMatrix state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot
              prevPivot := state.matrix[state.step][state.step]
              rowSwaps := state.rowSwaps
              singularStep := none }
            hp h_no_sing
      · rw [Matrix.noPivotLoop_done f state hDone] at h_no_sing ⊢
        exact hprev

/-- The `step` field of a no-pivot Bareiss state never decreases under further
loop iterations. -/
theorem noPivotLoop_step_monotone
    {n : Nat} (fuel : Nat) (state : Matrix.BareissState n) :
    state.step ≤ (Matrix.noPivotLoop fuel state).step := by
  induction fuel generalizing state with
  | zero =>
      show state.step ≤ state.step
      omega
  | succ f ih =>
      by_cases hDone : state.step + 1 < n
      · have hStepLt : state.step < n := Nat.lt_of_succ_lt hDone
        by_cases hp : state.matrix[state.step][state.step] = 0
        · rw [Matrix.noPivotLoop_singular_branch f state hDone hp]
          show state.step ≤ state.step
          omega
        · rw [Matrix.noPivotLoop_regular_branch f state hDone hp]
          have h_ih := ih
            { step := state.step + 1
              matrix := Matrix.stepMatrix state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot
              prevPivot := state.matrix[state.step][state.step]
              rowSwaps := state.rowSwaps
              singularStep := none }
          -- h_ih says state.step + 1 ≤ (noPivotLoop f next).step
          -- Want: state.step ≤ (noPivotLoop f next).step
          exact Nat.le_trans (Nat.le_succ _) h_ih
      · rw [Matrix.noPivotLoop_done f state hDone]
        show state.step ≤ state.step
        omega

/-- A singular step recorded by an initial no-pivot prefix remains the recorded
singular step after any further no-pivot iterations. -/
private theorem noPivotLoop_singularStep_of_prefix_singular
    {n : Nat} (a b : Nat) (state : Matrix.BareissState n)
    (h_init : state.singularStep = none) {s : Nat}
    (h_prefix : (Matrix.noPivotLoop a state).singularStep = some s) :
    (Matrix.noPivotLoop (a + b) state).singularStep = some s := by
  rw [noPivotLoop_add a b state]
  rcases noPivotLoop_singular_inv (n := n) a state h_init with h_none |
      ⟨k, h_sing, h_step, h_zero, h_bound⟩
  · rw [h_none] at h_prefix
    nomatch h_prefix
  · have hs : s = k.val := by
      rw [h_sing] at h_prefix
      injection h_prefix with h
      exact h.symm
    have hDone :
        (Matrix.noPivotLoop a state).step + 1 < n := by
      rw [h_step]
      exact h_bound
    have hidx :
        (⟨(Matrix.noPivotLoop a state).step, Nat.lt_of_succ_lt hDone⟩ : Fin n) = k :=
      Fin.ext h_step
    have hp :
        (Matrix.noPivotLoop a state).matrix[
            (⟨(Matrix.noPivotLoop a state).step,
              Nat.lt_of_succ_lt hDone⟩ : Fin n)][
            (⟨(Matrix.noPivotLoop a state).step,
              Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0 := by
      have h_lift := congrArg
        (fun (idx : Fin n) => (Matrix.noPivotLoop a state).matrix[idx][idx])
        hidx
      exact h_lift.trans h_zero
    have hsing_state :
        (Matrix.noPivotLoop a state).singularStep =
          some (Matrix.noPivotLoop a state).step := by
      rw [h_sing, h_step]
    rw [noPivotLoop_id_at_singular_fixedpoint b _ hDone hp hsing_state]
    rw [hs]
    exact h_sing

/-- If a full no-pivot run has no singular step, every initial prefix run also
has no singular step. -/
private theorem noPivotLoop_prefix_none_of_final_none
    {n : Nat} (a b : Nat) (state : Matrix.BareissState n)
    (h_init : state.singularStep = none)
    (h_final : (Matrix.noPivotLoop (a + b) state).singularStep = none) :
    (Matrix.noPivotLoop a state).singularStep = none := by
  rcases noPivotLoop_singular_inv (n := n) a state h_init with h_none |
      ⟨k, h_sing, _h_step, _h_zero, _h_bound⟩
  · exact h_none
  · have h_persist :=
      noPivotLoop_singularStep_of_prefix_singular a b state h_init h_sing
    rw [h_final] at h_persist
    nomatch h_persist

/-- If the full run records its first singular step after `a`, then the prefix
of length `a` is non-singular. -/
private theorem noPivotLoop_prefix_none_of_final_singular_after
    {n : Nat} (a b : Nat) (state : Matrix.BareissState n)
    (h_init : state.singularStep = none) {s : Nat}
    (h_final : (Matrix.noPivotLoop (a + b) state).singularStep = some s)
    (hs_after : state.step + a ≤ s) :
    (Matrix.noPivotLoop a state).singularStep = none := by
  rcases noPivotLoop_singular_inv (n := n) a state h_init with h_none |
      ⟨k, h_sing, _h_step, _h_zero, _h_bound⟩
  · exact h_none
  · have h_persist :=
      noPivotLoop_singularStep_of_prefix_singular a b state h_init h_sing
    rw [h_final] at h_persist
    injection h_persist with hks
    have hk_lt : k.val < state.step + a :=
      noPivotLoop_singularStep_lt a state h_init k.val h_sing
    omega

/-- No-pivot Bareiss projection at the `gramDetVecEntry` diagonal slot:
running `Matrix.noPivotLoop r` from the initial state on the full Gram
matrix and on its `(r+1)`-leading prefix yields states whose `(r, r)`
diagonal entry agrees (after the leading-prefix identification) and
whose `singularStep` field agrees. This is the executable-loop
projection needed by the parent assembly of
`gramDetVecEntry_eq_leadingPrefix_bareiss`. -/
private theorem noPivotLoop_full_eq_leadingPrefix_at_gramDetVecEntry
    (b : Matrix Int n m) (r : Nat) (hr : r < n) :
    let GM := Matrix.gramMatrix b
    let hK : r + 1 ≤ n := Nat.succ_le_of_lt hr
    let LP := Matrix.leadingPrefix GM (r + 1) hK
    let s_full := Matrix.noPivotLoop r (Matrix.noPivotInitialState GM)
    let s_pref := Matrix.noPivotLoop r (Matrix.noPivotInitialState LP)
    s_full.matrix[(⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] =
        s_pref.matrix[(⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1))][(⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1))]
      ∧ s_full.singularStep = s_pref.singularStep := by
  intro GM hK LP s_full s_pref
  have h_sync := noPivotLoop_sync_leadingPrefix_aux hK r
    (Matrix.noPivotInitialState GM) (Matrix.noPivotInitialState LP)
    rfl rfl rfl rfl rfl
    (show r + (Matrix.noPivotInitialState GM).step < r + 1 by
      simp [Matrix.noPivotInitialState])
  obtain ⟨_, _, _, h_sing, h_mat⟩ := h_sync
  refine ⟨?_, h_sing⟩
  -- Diagonal: the (r, r) entry of s_full agrees with the (r, r) entry of s_pref via the
  -- leading-prefix identification.
  have hcongr := congrArg
    (fun (M : Matrix Int (r + 1) (r + 1)) =>
      M[(⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1))][(⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1))])
    h_mat
  simp only [Matrix.leadingPrefix_entry] at hcongr
  -- hcongr's LHS index in Fin n has val = r; same as the goal's LHS index.
  exact hcongr

/-- The `gramDetVecEntry` slot at index `r + 1` for the no-pivot Bareiss pass
on `M : Matrix Int n n` is determined by the intermediate state after `r`
iterations of `Matrix.noPivotLoop`: the iterations from `r` to `n` either
leave the state unchanged (when a singular step is already recorded, by the
singular fixed point) or preserve the `(r, r)` diagonal entry and only
record singularities at steps `≥ r`, which the slot's match resolves to
the same natural value. -/
private theorem gramDetVecEntry_bareissNoPivot_eq_at_r
    {n : Nat} (M : Matrix Int n n) (r : Nat) (hr : r < n) :
    gramDetVecEntry (Matrix.bareissNoPivotData M) ⟨r + 1, Nat.succ_lt_succ hr⟩ =
      gramDetVecEntry
        (Matrix.finish (Matrix.noPivotLoop r (Matrix.noPivotInitialState M)))
        ⟨r + 1, Nat.succ_lt_succ hr⟩ := by
  have h_factor : Matrix.noPivotLoop n (Matrix.noPivotInitialState M) =
      Matrix.noPivotLoop (n - r) (Matrix.noPivotLoop r (Matrix.noPivotInitialState M)) := by
    have h_add := noPivotLoop_add r (n - r) (Matrix.noPivotInitialState M)
    have h_split : r + (n - r) = n := by omega
    rw [h_split] at h_add
    exact h_add
  show gramDetVecEntry (Matrix.finish (Matrix.noPivotLoop n (Matrix.noPivotInitialState M)))
      ⟨r + 1, Nat.succ_lt_succ hr⟩ = _
  rw [h_factor]
  rcases noPivotLoop_singular_inv (n := n) r (Matrix.noPivotInitialState M) rfl with
    h_r_none | ⟨k_r, h_r_sing, h_r_step, h_r_zero, h_r_klt⟩
  · -- After r iterations, no singular step recorded yet.
    have h_step_r :
        (Matrix.noPivotLoop r (Matrix.noPivotInitialState M)).step = r := by
      have := noPivotLoop_step_eq_add_of_singularStep_none r
        (Matrix.noPivotInitialState M) rfl (show 0 + r + 1 ≤ n by omega) h_r_none
      simpa [Matrix.noPivotInitialState] using this
    have h_diag_preserved :
        (Matrix.noPivotLoop (n - r) (Matrix.noPivotLoop r
            (Matrix.noPivotInitialState M))).matrix[(⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] =
          (Matrix.noPivotLoop r (Matrix.noPivotInitialState M)).matrix[(⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] := by
      apply Matrix.noPivotLoop_diag_of_le_step
      show r ≤ (Matrix.noPivotLoop r (Matrix.noPivotInitialState M)).step
      rw [h_step_r]
      exact Nat.le_refl r
    rcases noPivotLoop_singular_inv (n := n) (n - r)
        (Matrix.noPivotLoop r (Matrix.noPivotInitialState M)) h_r_none with
      h_extra_none | ⟨k, h_extra_sing, h_extra_step, h_extra_zero, h_extra_klt⟩
    · -- No singularity introduced by the extra iterations.
      simp only [gramDetVecEntry, Matrix.finish, bareissDiagNat,
        h_extra_none, h_r_none]
      exact congrArg Int.toNat h_diag_preserved
    · -- Singularity introduced at step k.val ≥ r.
      have h_step_mono := noPivotLoop_step_monotone (n - r)
        (Matrix.noPivotLoop r (Matrix.noPivotInitialState M))
      have h_k_ge_r : r ≤ k.val := by
        rw [← h_step_r, ← h_extra_step]; exact h_step_mono
      simp only [gramDetVecEntry, Matrix.finish, bareissDiagNat,
        h_extra_sing, h_r_none]
      by_cases h : k.val < r + 1
      · -- k.val = r, so the (r, r) entry was zero.
        have h_k_eq_r : k.val = r := by omega
        rw [if_pos h]
        have h_k_idx : k = ⟨r, hr⟩ := Fin.ext h_k_eq_r
        rw [h_k_idx] at h_extra_zero
        have h_diag_zero :
            (Matrix.noPivotLoop r (Matrix.noPivotInitialState M)).matrix[(⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] = 0 := by
          rw [← h_diag_preserved]; exact h_extra_zero
        exact (congrArg Int.toNat h_diag_zero).symm
      · rw [if_neg h]
        exact congrArg Int.toNat h_diag_preserved
  · -- After r iterations, a singular step was already recorded.
    have h_extra_id :
        Matrix.noPivotLoop (n - r) (Matrix.noPivotLoop r (Matrix.noPivotInitialState M)) =
          Matrix.noPivotLoop r (Matrix.noPivotInitialState M) := by
      have h_hDone :
          (Matrix.noPivotLoop r (Matrix.noPivotInitialState M)).step + 1 < n := by
        rw [h_r_step]; exact h_r_klt
      have h_idx :
          (⟨(Matrix.noPivotLoop r (Matrix.noPivotInitialState M)).step,
              Nat.lt_of_succ_lt h_hDone⟩ : Fin n) = k_r :=
        Fin.ext h_r_step
      have h_hp :
          (Matrix.noPivotLoop r (Matrix.noPivotInitialState M)).matrix[
              (⟨(Matrix.noPivotLoop r (Matrix.noPivotInitialState M)).step,
                  Nat.lt_of_succ_lt h_hDone⟩ : Fin n)][
              (⟨(Matrix.noPivotLoop r (Matrix.noPivotInitialState M)).step,
                  Nat.lt_of_succ_lt h_hDone⟩ : Fin n)] = 0 := by
        have h_lift := congrArg
          (fun (i : Fin n) =>
            (Matrix.noPivotLoop r (Matrix.noPivotInitialState M)).matrix[i][i])
          h_idx
        exact h_lift.trans h_r_zero
      have h_hsing :
          (Matrix.noPivotLoop r (Matrix.noPivotInitialState M)).singularStep =
            some (Matrix.noPivotLoop r (Matrix.noPivotInitialState M)).step := by
        rw [h_r_sing, h_r_step]
      exact noPivotLoop_id_at_singular_fixedpoint (n - r) _ h_hDone h_hp h_hsing
    rw [h_extra_id]

/-- The `gramDetVecEntry` slot at index `r + 1` for the no-pivot Bareiss pass
over the full Gram matrix agrees with the same slot for the no-pivot Bareiss
pass over its `(r + 1)` leading prefix. This is the `bareissNoPivotData`-level
wrapper assembled from the `r`-iteration loop sync. -/
theorem gramDetVecEntry_bareissNoPivot_full_eq_leadingPrefix
    (b : Matrix Int n m) (r : Nat) (hr : r < n) :
    gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
        ⟨r + 1, Nat.succ_lt_succ hr⟩ =
      gramDetVecEntry
        (Matrix.bareissNoPivotData
          (Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1)
            (Nat.succ_le_of_lt hr)))
        ⟨r + 1, Nat.lt_succ_self _⟩ := by
  obtain ⟨h_diag, h_sing⟩ :=
    noPivotLoop_full_eq_leadingPrefix_at_gramDetVecEntry (b := b) r hr
  rw [gramDetVecEntry_bareissNoPivot_eq_at_r (Matrix.gramMatrix b) r hr]
  rw [gramDetVecEntry_bareissNoPivot_eq_at_r
    (Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1) (Nat.succ_le_of_lt hr)) r
    (Nat.lt_succ_self r)]
  -- Reduce both gramDetVecEntry calls to their match form, then case on the
  -- shared singularStep value.
  simp only [gramDetVecEntry, Matrix.finish, bareissDiagNat]
  rw [← h_sing]
  generalize hs :
      (Matrix.noPivotLoop r (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = ss
  cases ss with
  | none =>
      dsimp only
      exact congrArg Int.toNat h_diag
  | some s_val =>
      dsimp only
      by_cases h : s_val < r + 1
      · rw [if_pos h, if_pos h]
      · rw [if_neg h, if_neg h]
        exact congrArg Int.toNat h_diag

/-- Signed diagonal projection for a non-singular target prefix: the final
no-pivot full-Gram diagonal at `r` is the public Bareiss determinant of the
`(r + 1)` leading prefix. -/
theorem bareissNoPivotData_diag_eq_leadingPrefix_bareiss_of_prefix_nonsingular
    (b : Matrix Int n m) (r : Nat) (hr : r < n)
    (h_nonsing :
      (Matrix.noPivotLoop r
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    (Matrix.bareissNoPivotData (Matrix.gramMatrix b)).matrix[
        (⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] =
      Matrix.bareiss
        (Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1)
          (Nat.succ_le_of_lt hr)) := by
  let GM := Matrix.gramMatrix b
  let init := Matrix.noPivotInitialState GM
  let fullAtR := Matrix.noPivotLoop r init
  let LP := Matrix.leadingPrefix GM (r + 1) (Nat.succ_le_of_lt hr)
  have h_step_r : fullAtR.step = r := by
    have h_room : init.step + r + 1 ≤ n := by
      simp [init, Matrix.noPivotInitialState]
      omega
    have h := noPivotLoop_step_eq_add_of_singularStep_none r init rfl h_room h_nonsing
    simpa [fullAtR, init, Matrix.noPivotInitialState] using h
  have h_factor :
      Matrix.noPivotLoop n init = Matrix.noPivotLoop (n - r) fullAtR := by
    have h_add := noPivotLoop_add r (n - r) init
    have h_split : r + (n - r) = n := by omega
    simpa [fullAtR, h_split] using h_add
  have h_final_diag :
      (Matrix.noPivotLoop n init).matrix[(⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] =
        fullAtR.matrix[(⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] := by
    rw [h_factor]
    have h_le : (⟨r, hr⟩ : Fin n).val ≤ fullAtR.step := by
      change r ≤ fullAtR.step
      rw [h_step_r]
      exact Nat.le_refl r
    exact Matrix.noPivotLoop_diag_of_le_step (n - r) fullAtR (⟨r, hr⟩ : Fin n) h_le
  obtain ⟨h_diag, h_sing⟩ :=
    noPivotLoop_full_eq_leadingPrefix_at_gramDetVecEntry (b := b) r hr
  have h_pref_nonsing :
      (Matrix.noPivotLoop r (Matrix.noPivotInitialState LP)).singularStep = none := by
    rw [← h_sing]
    exact h_nonsing
  have h_bareiss :=
    Matrix.bareiss_eq_noPivotLoop_last_of_no_singular (M := LP) h_pref_nonsing
  calc
    (Matrix.bareissNoPivotData (Matrix.gramMatrix b)).matrix[
        (⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] =
        fullAtR.matrix[(⟨r, hr⟩ : Fin n)][(⟨r, hr⟩ : Fin n)] := by
          simpa [Matrix.bareissNoPivotData, Matrix.finish, GM, init, fullAtR] using
            h_final_diag
    _ =
        (Matrix.noPivotLoop r (Matrix.noPivotInitialState LP)).matrix[
          (⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1))][
          (⟨r, Nat.lt_succ_self r⟩ : Fin (r + 1))] := by
          simpa [GM, LP, fullAtR, init] using h_diag
    _ = Matrix.bareiss LP := by
          simpa [LP, Fin.last] using h_bareiss.symm

/-! ### Gram row-span invariant for no-pivot Bareiss -/

/-- Row-vector interpretation of the trailing block during a no-pivot Bareiss
pass over a Gram matrix.  Each active trailing row carries an explicit integer
coefficient vector `coeff i` such that the represented row is
`Matrix.rowCombination b (coeff i)`, supported at coordinates `≤ i.val`, and
each matrix entry in that trailing row is its inner product against the
corresponding original row. -/
private structure BareissGramRowInvariant (b : Matrix Int n m)
    (state : Matrix.BareissState n) where
  coeff : Fin n → Vector Int n
  coeff_supp : ∀ i k : Fin n, state.step ≤ i.val → i.val < k.val →
    (coeff i)[k] = 0
  entry_eq_dot : ∀ i j : Fin n, state.step ≤ i.val →
    state.matrix[i][j] =
      Matrix.dot (Matrix.rowCombination b (coeff i)) (b.row j)

/-- The initial no-pivot Gram state satisfies the row-coefficient invariant
with each row represented by the standard basis vector `eᵢ`. -/
private def bareissGramRowInvariant_initial (b : Matrix Int n m) :
    BareissGramRowInvariant b
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)) := by
  refine
    { coeff := fun i => Vector.ofFn fun k : Fin n => if i = k then 1 else 0
      coeff_supp := ?_
      entry_eq_dot := ?_ }
  · intro i k _hi hik
    by_cases h : i = k
    · subst k
      omega
    · simp [h]
  · intro i j _hi
    have hsingle :
        Matrix.rowCombination b
            (Vector.ofFn fun k : Fin n => if i = k then (1 : Int) else 0) =
          b.row i :=
      Matrix.IsRREF.rowCombination_single (M := b) i
    rw [hsingle]
    simp [Matrix.noPivotInitialState, Matrix.gramMatrix, Matrix.ofFn, Matrix.dot]

private theorem foldl_sum_bareiss_row_update
    {α : Type u} (xs : List α) (x y : Int) (u v w : α → Int)
    (accU accV : Int) :
    xs.foldl
        (fun acc a => acc + ((x * u a - y * v a) * w a))
        (x * accU - y * accV) =
      x * xs.foldl (fun acc a => acc + u a * w a) accU -
        y * xs.foldl (fun acc a => acc + v a * w a) accV := by
  induction xs generalizing accU accV with
  | nil =>
      simp
  | cons a xs ih =>
      simp only [List.foldl_cons]
      have hstep :
          x * accU - y * accV + ((x * u a - y * v a) * w a) =
            x * (accU + u a * w a) - y * (accV + v a * w a) := by
        grind
      rw [hstep]
      exact ih (accU + u a * w a) (accV + v a * w a)

private theorem dot_bareiss_row_update_left
    (x y : Int) (u v w : Vector Int m) :
    Matrix.dot (Vector.ofFn fun a : Fin m => x * u[a] - y * v[a]) w =
      x * Matrix.dot u w - y * Matrix.dot v w := by
  unfold Matrix.dot Hex.Vector.dotProduct
  simpa using
    foldl_sum_bareiss_row_update
      (xs := List.finRange m) x y
      (fun a : Fin m => u[a])
      (fun a : Fin m => v[a])
      (fun a : Fin m => w[a])
      0 0

private theorem foldl_sum_bareiss_row_update_right
    {α : Type u} (xs : List α) (x y : Int) (u v w : α → Int)
    (accU accV : Int) :
    xs.foldl
        (fun acc a => acc + (w a * (x * u a - y * v a)))
        (x * accU - y * accV) =
      x * xs.foldl (fun acc a => acc + w a * u a) accU -
        y * xs.foldl (fun acc a => acc + w a * v a) accV := by
  induction xs generalizing accU accV with
  | nil =>
      simp
  | cons a xs ih =>
      simp only [List.foldl_cons]
      have hstep :
          x * accU - y * accV + (w a * (x * u a - y * v a)) =
            x * (accU + w a * u a) - y * (accV + w a * v a) := by
        grind
      rw [hstep]
      exact ih (accU + w a * u a) (accV + w a * v a)

private theorem dot_bareiss_row_update_right
    (x y : Int) (w u v : Vector Int m) :
    Matrix.dot w (Vector.ofFn fun a : Fin m => x * u[a] - y * v[a]) =
      x * Matrix.dot w u - y * Matrix.dot w v := by
  unfold Matrix.dot Hex.Vector.dotProduct
  simpa using
    foldl_sum_bareiss_row_update_right
      (xs := List.finRange m) x y
      (fun a : Fin m => u[a])
      (fun a : Fin m => v[a])
      (fun a : Fin m => w[a])
      0 0

private theorem rowCombination_bareiss_coeff_update
    (M : Matrix Int n m) (x y : Int) (c d : Vector Int n) :
    Matrix.rowCombination M (Vector.ofFn fun a : Fin n => x * c[a] - y * d[a]) =
      Vector.ofFn fun j : Fin m =>
        x * (Matrix.rowCombination M c)[j] - y * (Matrix.rowCombination M d)[j] := by
  apply Vector.ext
  intro j hj
  let jf : Fin m := ⟨j, hj⟩
  show
      (Matrix.rowCombination M (Vector.ofFn fun a : Fin n => x * c[a] - y * d[a]))[jf] =
        (Vector.ofFn fun j : Fin m =>
          x * (Matrix.rowCombination M c)[j] - y * (Matrix.rowCombination M d)[j])[jf]
  unfold Matrix.rowCombination
  have h_rhs :
      (Vector.ofFn fun j : Fin m => x * (M.transpose * c)[j] - y * (M.transpose * d)[j])[jf] =
        x * (M.transpose * c)[jf] - y * (M.transpose * d)[jf] := by
    change (Vector.ofFn fun j : Fin m =>
      x * (M.transpose * c)[j] - y * (M.transpose * d)[j]).get jf =
        x * (M.transpose * c)[jf] - y * (M.transpose * d)[jf]
    rw [Vector.get_ofFn]
  rw [h_rhs]
  repeat rw [Matrix.mulVec_getElem]
  exact dot_bareiss_row_update_right x y ((Matrix.transpose M).row jf) c d

private theorem exactDiv_eq_of_eq_mul_right
    {num denom q : Int} (hdenom : denom ≠ 0) (hnum : num = q * denom) :
  Matrix.exactDiv num denom = q := by
  have hnum' : num = denom * q := by
    grind
  have hdvd : denom ∣ num := by
    refine ⟨q, ?_⟩
    exact hnum'
  rw [Matrix.exactDiv_eq_divExact hdvd, Int.divExact_eq_ediv hdvd]
  exact Int.ediv_eq_of_eq_mul_left hdenom hnum

private theorem vector_exactDiv_eq_of_eq_mul_right
    {denom : Int} (hdenom : denom ≠ 0) (num q : Fin n → Int)
    (hnum : ∀ a : Fin n, num a = q a * denom) :
    (Vector.ofFn fun a : Fin n => Matrix.exactDiv (num a) denom) =
      Vector.ofFn q := by
  apply Vector.ext
  intro a ha
  let af : Fin n := ⟨a, ha⟩
  simp [exactDiv_eq_of_eq_mul_right hdenom (hnum af), af]

private theorem rowCombination_exactDiv_eq_of_eq_mul_right
    (M : Matrix Int n m) {denom : Int} (hdenom : denom ≠ 0)
    (num q : Fin n → Int) (hnum : ∀ a : Fin n, num a = q a * denom) :
    Matrix.rowCombination M (Vector.ofFn fun a : Fin n => Matrix.exactDiv (num a) denom) =
      Matrix.rowCombination M (Vector.ofFn q) := by
  rw [vector_exactDiv_eq_of_eq_mul_right hdenom num q hnum]

private theorem dot_rowCombination_exactDiv_eq_of_eq_mul_right
    (M : Matrix Int n m) {denom : Int} (hdenom : denom ≠ 0)
    (num q : Fin n → Int) (hnum : ∀ a : Fin n, num a = q a * denom)
    (w : Vector Int m) :
    Matrix.dot
        (Matrix.rowCombination M
          (Vector.ofFn fun a : Fin n => Matrix.exactDiv (num a) denom))
        w =
      Matrix.dot (Matrix.rowCombination M (Vector.ofFn q)) w := by
  rw [rowCombination_exactDiv_eq_of_eq_mul_right M hdenom num q hnum]

/-- Project the explicit coefficient witness for the row at index `i`. -/
private def bareissGramRowInvariantCoeff
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    (hinv : BareissGramRowInvariant b state) (i : Fin n) : Vector Int n :=
  hinv.coeff i

private theorem bareissGramRowInvariantCoeff_support
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    (hinv : BareissGramRowInvariant b state) (i : Fin n)
    (hi : state.step ≤ i.val) :
    ∀ k : Fin n, i.val < k.val →
      (bareissGramRowInvariantCoeff hinv i)[k] = 0 :=
  fun k hik => hinv.coeff_supp i k hi hik

private theorem bareissGramRowInvariantCoeff_row
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    (hinv : BareissGramRowInvariant b state) (i : Fin n) :
    Matrix.rowCombination b (bareissGramRowInvariantCoeff hinv i) =
      Matrix.rowCombination b (hinv.coeff i) := rfl

/-- Coefficient witness produced by one regular Bareiss step on the row at
index `i`.  The functional shape mirrors the row update on the matrix side. -/
private def bareissGramRowInvariantStepCoeff
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    (hinv : BareissGramRowInvariant b state)
    (hnext : state.step + 1 < n) (i : Fin n) (_hi : state.step + 1 ≤ i.val) :
    Vector Int n :=
  let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hnext⟩
  Vector.ofFn fun a : Fin n =>
    Matrix.exactDiv
      (state.matrix[k][k] * (hinv.coeff i)[a] -
        state.matrix[i][k] * (hinv.coeff k)[a])
      state.prevPivot

/-- Coefficient-level exact-division provenance for one regular Gram-row
Bareiss step.  The quotient vector is kept separate from
`bareissGramRowInvariantStepCoeff` so later row-entry proofs can consume the
integer divisibility witness before projecting back to the existing exact-div
coefficient API. -/
private structure BareissGramRegularStepQuotient
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    (hinv : BareissGramRowInvariant b state)
    (hnext : state.step + 1 < n) (i : Fin n) (_hi : state.step + 1 ≤ i.val) where
  q : Fin n → Int
  coeff_num_eq_mul :
    let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hnext⟩
    ∀ a : Fin n,
      state.matrix[k][k] * (hinv.coeff i)[a] -
        state.matrix[i][k] * (hinv.coeff k)[a] =
          q a * state.prevPivot

/-- Initial no-pivot Gram trajectory specialization of the regular-step
coefficient quotient package. -/
private abbrev BareissGramInitialRegularStepQuotient
    (b : Matrix Int n m) (fuel : Nat)
    (hinv : BareissGramRowInvariant b
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))))
    (hnext :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n)
    (i : Fin n)
    (hi :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 ≤ i.val) :
    Type :=
  BareissGramRegularStepQuotient hinv hnext i hi

private theorem bareissGramRegularStepQuotient_stepCoeff_get
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    {hinv : BareissGramRowInvariant b state}
    {hnext : state.step + 1 < n} {i : Fin n} {hi : state.step + 1 ≤ i.val}
    (hprev : state.prevPivot ≠ 0)
    (hq : BareissGramRegularStepQuotient hinv hnext i hi) (a : Fin n) :
    (bareissGramRowInvariantStepCoeff hinv hnext i hi)[a] = hq.q a := by
  dsimp [bareissGramRowInvariantStepCoeff]
  rw [Vector.getElem_ofFn]
  exact exactDiv_eq_of_eq_mul_right hprev (hq.coeff_num_eq_mul a)

private theorem bareissGramRegularStepQuotient_stepCoeff_eq
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    {hinv : BareissGramRowInvariant b state}
    {hnext : state.step + 1 < n} {i : Fin n} {hi : state.step + 1 ≤ i.val}
    (hprev : state.prevPivot ≠ 0)
    (hq : BareissGramRegularStepQuotient hinv hnext i hi) :
    bareissGramRowInvariantStepCoeff hinv hnext i hi = Vector.ofFn hq.q := by
  apply Vector.ext
  intro a ha
  let af : Fin n := ⟨a, ha⟩
  simpa [af] using
    bareissGramRegularStepQuotient_stepCoeff_get
      (hinv := hinv) (hnext := hnext) (i := i) (hi := hi) hprev hq af

private theorem rowCombination_bareissGramRegularStepQuotient
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    {hinv : BareissGramRowInvariant b state}
    {hnext : state.step + 1 < n} {i : Fin n} {hi : state.step + 1 ≤ i.val}
    (hprev : state.prevPivot ≠ 0)
    (hq : BareissGramRegularStepQuotient hinv hnext i hi) :
    Matrix.rowCombination b (bareissGramRowInvariantStepCoeff hinv hnext i hi) =
      Matrix.rowCombination b (Vector.ofFn hq.q) := by
  rw [bareissGramRegularStepQuotient_stepCoeff_eq hprev hq]

private theorem dot_rowCombination_bareissGramRegularStepQuotient
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    {hinv : BareissGramRowInvariant b state}
    {hnext : state.step + 1 < n} {i : Fin n} {hi : state.step + 1 ≤ i.val}
    (hprev : state.prevPivot ≠ 0)
    (hq : BareissGramRegularStepQuotient hinv hnext i hi)
    (w : Vector Int m) :
    Matrix.dot
        (Matrix.rowCombination b
          (bareissGramRowInvariantStepCoeff hinv hnext i hi))
        w =
      Matrix.dot (Matrix.rowCombination b (Vector.ofFn hq.q)) w := by
  rw [rowCombination_bareissGramRegularStepQuotient hprev hq]

private theorem bareissGramRowInvariantStepCoeff_support
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    (hinv : BareissGramRowInvariant b state)
    (hnext : state.step + 1 < n) (i : Fin n) (hi : state.step + 1 ≤ i.val) :
    ∀ a : Fin n, i.val < a.val →
      (bareissGramRowInvariantStepCoeff hinv hnext i hi)[a] = 0 := by
  intro a hia
  dsimp [bareissGramRowInvariantStepCoeff]
  rw [Vector.getElem_ofFn]
  let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hnext⟩
  have h_i : state.step ≤ i.val := Nat.le_trans (Nat.le_succ state.step) hi
  have h_k : state.step ≤ k.val := Nat.le_refl _
  have hci : (hinv.coeff i)[a] = 0 := hinv.coeff_supp i a h_i hia
  have hk_lt_i : k.val < i.val := by
    dsimp [k]
    omega
  have hka : k.val < a.val := Nat.lt_trans hk_lt_i hia
  have hck : (hinv.coeff k)[a] = 0 := hinv.coeff_supp k a h_k hka
  have hciNat : (hinv.coeff i)[a.val] = 0 := by simpa using hci
  have hckNat :
      (hinv.coeff
        (⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hnext⟩ : Fin n))[a.val] = 0 := by
    simpa [k] using hck
  simp [hciNat, hckNat, Matrix.exactDiv]

/-- Right-scalar linearity of the dot product against a `rowCombination` whose
coefficient vector is multiplied pointwise by a constant on the right.  Used
to factor the Bareiss exact-division denominator out of a quotient-backed row
combination. -/
private theorem dot_rowCombination_mul_right_int
    (b : Matrix Int n m) (f : Fin n → Int) (s : Int) (w : Vector Int m) :
    Matrix.dot
        (Matrix.rowCombination b (Vector.ofFn fun a : Fin n => f a * s)) w =
      Matrix.dot (Matrix.rowCombination b (Vector.ofFn f)) w * s := by
  have h_eq_input :
      (Vector.ofFn fun a : Fin n => f a * s) =
        Vector.ofFn fun a : Fin n =>
          s * (Vector.ofFn f)[a] - 0 * (Vector.ofFn f)[a] := by
    apply Vector.ext
    intro a ha
    simp only [Vector.getElem_ofFn]
    grind
  rw [h_eq_input]
  rw [rowCombination_bareiss_coeff_update b s 0 (Vector.ofFn f) (Vector.ofFn f)]
  rw [dot_bareiss_row_update_left s 0
    (Matrix.rowCombination b (Vector.ofFn f))
    (Matrix.rowCombination b (Vector.ofFn f)) w]
  grind

/-- Row-entry algebra for one regular Gram-row Bareiss step.  Consuming the
quotient-coefficient package `BareissGramRegularStepQuotient` together with a
nonzero `prevPivot` and the already-processed-column zero entries gives the
exact row-entry relation for `Matrix.stepMatrix` at row `i` and any column
`j`.  Covers the three column regimes: `j.val < state.step` (already-cleared
column, both sides zero), `j.val = state.step` (pivot column below the pivot,
both sides zero), and `state.step < j.val` (trailing block, `exactDiv` of the
Bareiss numerator). -/
private theorem bareissGramRegularStep_entry_eq_dot
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    {hinv : BareissGramRowInvariant b state}
    {hnext : state.step + 1 < n} {i : Fin n} {hi : state.step + 1 ≤ i.val}
    (hprev : state.prevPivot ≠ 0)
    (hq : BareissGramRegularStepQuotient hinv hnext i hi)
    (h_processed : ∀ i' : Fin n, state.step ≤ i'.val →
      ∀ j' : Fin n, j'.val < state.step → state.matrix[i'][j'] = 0)
    (j : Fin n) :
    (Matrix.stepMatrix state.matrix state.step
        state.matrix[state.step][state.step] state.prevPivot)[i][j] =
      Matrix.dot
        (Matrix.rowCombination b
          (bareissGramRowInvariantStepCoeff hinv hnext i hi))
        (b.row j) := by
  let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hnext⟩
  have hk_val : k.val = state.step := rfl
  have h_step_le_i : state.step ≤ i.val := Nat.le_trans (Nat.le_succ _) hi
  have h_step_lt_i : state.step < i.val := hi
  have h_step_le_k : state.step ≤ k.val := Nat.le_refl _
  let lhsNum : Int :=
    state.matrix[k][k] * state.matrix[i][j] - state.matrix[i][k] * state.matrix[k][j]
  have hLHS_num : lhsNum =
      state.matrix[k][k] * state.matrix[i][j] -
        state.matrix[i][k] * state.matrix[k][j] := rfl
  -- Claim A: the dot product of the "numerator-side" row combination is lhsNum.
  have h_dot_num :
      Matrix.dot
          (Matrix.rowCombination b
            (Vector.ofFn fun a : Fin n =>
              state.matrix[k][k] * (hinv.coeff i)[a] -
                state.matrix[i][k] * (hinv.coeff k)[a]))
          (b.row j) = lhsNum := by
    rw [rowCombination_bareiss_coeff_update b
      state.matrix[k][k] state.matrix[i][k] (hinv.coeff i) (hinv.coeff k)]
    rw [dot_bareiss_row_update_left
      state.matrix[k][k] state.matrix[i][k]
      (Matrix.rowCombination b (hinv.coeff i))
      (Matrix.rowCombination b (hinv.coeff k))
      (b.row j)]
    rw [← hinv.entry_eq_dot i j h_step_le_i,
        ← hinv.entry_eq_dot k j h_step_le_k]
  -- Claim B: the dot product of the step coefficient row combination equals
  -- `exactDiv lhsNum prevPivot`.
  have h_dot_step :
      Matrix.dot
          (Matrix.rowCombination b
            (bareissGramRowInvariantStepCoeff hinv hnext i hi))
          (b.row j) = Matrix.exactDiv lhsNum state.prevPivot := by
    rw [rowCombination_bareissGramRegularStepQuotient hprev hq]
    refine (exactDiv_eq_of_eq_mul_right hprev ?_).symm
    have h_dot_mul :=
      dot_rowCombination_mul_right_int b hq.q state.prevPivot (b.row j)
    rw [← h_dot_mul]
    have h_q_eq_num :
        (Vector.ofFn fun a : Fin n => hq.q a * state.prevPivot) =
          (Vector.ofFn fun a : Fin n =>
            state.matrix[k][k] * (hinv.coeff i)[a] -
              state.matrix[i][k] * (hinv.coeff k)[a]) := by
      apply Vector.ext
      intro a ha
      rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
      exact (hq.coeff_num_eq_mul ⟨a, ha⟩).symm
    rw [h_q_eq_num]
    exact h_dot_num.symm
  -- Case split on `j.val` against `state.step`.
  by_cases hjk : state.step < j.val
  · -- Trailing block: stepMatrix is the Bareiss exactDiv update.
    rw [Matrix.stepMatrix_update_eq state.matrix state.step
      state.matrix[state.step][state.step] state.prevPivot i j h_step_lt_i hjk]
    rw [h_dot_step]
    rfl
  · by_cases hjeq : j.val = state.step
    · -- Pivot column, below the pivot: stepMatrix entry is 0, and `lhsNum = 0`.
      rw [Matrix.stepMatrix_pivot_col_below state.matrix state.step
        state.matrix[state.step][state.step] state.prevPivot i j h_step_lt_i hjeq]
      rw [h_dot_step]
      have h_j_eq_k : j = k := Fin.ext (by rw [hjeq, hk_val])
      have h_lhs_num_zero : lhsNum = 0 := by
        rw [hLHS_num, h_j_eq_k]; grind
      rw [h_lhs_num_zero]
      symm
      exact exactDiv_eq_of_eq_mul_right hprev
        (by grind : (0 : Int) = 0 * state.prevPivot)
    · -- Already-processed column: stepMatrix carries over, both sides zero.
      have hj_lt : j.val < state.step :=
        Nat.lt_of_le_of_ne (Nat.le_of_not_lt hjk) hjeq
      have h_not_trail : ¬ (state.step < i.val ∧ state.step < j.val) := by
        intro ⟨_, h2⟩; exact absurd h2 (Nat.not_lt_of_le (Nat.le_of_lt hj_lt))
      have h_not_col : ¬ (state.step < i.val ∧ j.val = state.step) := by
        intro ⟨_, h2⟩; exact hjeq h2
      rw [Matrix.stepMatrix_eq_of_not_update state.matrix state.step
        state.matrix[state.step][state.step] state.prevPivot i j h_not_trail h_not_col]
      have h_i_j_zero : state.matrix[i][j] = 0 := h_processed i h_step_le_i j hj_lt
      have h_k_j_zero : state.matrix[k][j] = 0 := h_processed k h_step_le_k j hj_lt
      have h_lhs_num_zero : lhsNum = 0 := by
        rw [hLHS_num, h_i_j_zero, h_k_j_zero]; grind
      rw [h_dot_step, h_lhs_num_zero, h_i_j_zero]
      symm
      exact exactDiv_eq_of_eq_mul_right hprev
        (by grind : (0 : Int) = 0 * state.prevPivot)

/-- One regular no-pivot Bareiss step preserves the Gram row-coefficient
invariant, provided the later loop proof supplies the exact-division entry
relation for the fraction-free updated row combinations. -/
private def bareissGramRowInvariant_regular_step
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    (hnext : state.step + 1 < n)
    (_hp : state.matrix[state.step][state.step] ≠ 0)
    (hinv : BareissGramRowInvariant b state)
    (hentry :
      ∀ i j : Fin n, (hi : state.step + 1 ≤ i.val) →
        (Matrix.stepMatrix state.matrix state.step
            state.matrix[state.step][state.step] state.prevPivot)[i][j] =
          Matrix.dot
            (Matrix.rowCombination b
              (bareissGramRowInvariantStepCoeff hinv hnext i hi))
            (b.row j)) :
    BareissGramRowInvariant b
      { step := state.step + 1
        matrix := Matrix.stepMatrix state.matrix state.step
          state.matrix[state.step][state.step] state.prevPivot
        prevPivot := state.matrix[state.step][state.step]
        rowSwaps := state.rowSwaps
        singularStep := none } := by
  refine
    { coeff := fun i =>
        if hi : state.step + 1 ≤ i.val then
          bareissGramRowInvariantStepCoeff hinv hnext i hi
        else
          hinv.coeff i
      coeff_supp := ?_
      entry_eq_dot := ?_ }
  · intro i k hi hik
    have hi' : state.step + 1 ≤ i.val := hi
    simp [hi', bareissGramRowInvariantStepCoeff_support hinv hnext i hi' k hik]
  · intro i j hi
    have hi' : state.step + 1 ≤ i.val := hi
    simpa [hi'] using hentry i j hi'

/-- Extract the represented lattice row vector and entry equation carried by
`BareissGramRowInvariant`. This is the caller-facing shape needed by
singular no-pivot arguments: an active row of the current Bareiss matrix is a
dot product against an explicitly represented integer combination of input
rows. -/
private theorem bareissGramRowInvariant_exists_rowVec
    {b : Matrix Int n m} {state : Matrix.BareissState n}
    (hinv : BareissGramRowInvariant b state) (i j : Fin n)
    (hi : state.step ≤ i.val) :
    ∃ v : Vector Int m,
      (∃ c : Vector Int n,
        (∀ k : Fin n, i.val < k.val → c[k] = 0) ∧
          v = Matrix.rowCombination b c) ∧
        state.matrix[i][j] = Matrix.dot v (b.row j) := by
  refine ⟨Matrix.rowCombination b (hinv.coeff i), ?_, hinv.entry_eq_dot i j hi⟩
  exact ⟨hinv.coeff i, fun k hik => hinv.coeff_supp i k hi hik, rfl⟩

/-- Recursive preservation package for `Matrix.noPivotLoop`.  Every regular
step delegates the exact row-entry relation to the one-step package; done and
singular branches preserve the current coefficient witnesses unchanged. -/
private def bareissGramRowInvariant_noPivotLoop
    {b : Matrix Int n m} (fuel : Nat) {state : Matrix.BareissState n}
    (hinv : BareissGramRowInvariant b state)
    (hentry_regular :
      ∀ {state : Matrix.BareissState n},
        (hinv_state : BareissGramRowInvariant b state) →
        (hnext : state.step + 1 < n) →
        state.matrix[state.step][state.step] ≠ 0 →
        ∀ i j : Fin n, (hi : state.step + 1 ≤ i.val) →
          (Matrix.stepMatrix state.matrix state.step
              state.matrix[state.step][state.step] state.prevPivot)[i][j] =
            Matrix.dot
              (Matrix.rowCombination b
                (bareissGramRowInvariantStepCoeff
                  hinv_state hnext i hi))
              (b.row j)) :
    BareissGramRowInvariant b (Matrix.noPivotLoop fuel state) := by
  induction fuel generalizing state with
  | zero =>
      simpa [Matrix.noPivotLoop_zero_fuel] using hinv
  | succ fuel ih =>
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · rw [Matrix.noPivotLoop_singular_branch fuel state hDone hp]
          refine
            { coeff := hinv.coeff
              coeff_supp := ?_
              entry_eq_dot := ?_ }
          · simpa using hinv.coeff_supp
          · simpa using hinv.entry_eq_dot
        · rw [Matrix.noPivotLoop_regular_branch fuel state hDone hp]
          apply ih
          exact bareissGramRowInvariant_regular_step hDone hp hinv
            (hentry_regular hinv hDone hp)
      · rw [Matrix.noPivotLoop_done fuel state hDone]
        exact hinv

/-- If the initial no-pivot Gram pass reaches column `s` without recording a
singular step, its state step is exactly `s`.  This keeps the later singular
pivot argument from unfolding the loop just to align the searched column. -/
private theorem noPivotLoop_initial_gram_step_eq_of_prefix_none
    (b : Matrix Int n m) (s : Nat) (hs : s + 1 < n)
    (h_prefix_none :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    (Matrix.noPivotLoop s
      (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step = s := by
  have h_room :
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step + s + 1 ≤ n := by
    simp [Matrix.noPivotInitialState]
    omega
  have h_step :=
    Matrix.noPivotLoop_step_eq_add_of_singularStep_none s
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl h_room h_prefix_none
  simpa [Matrix.noPivotInitialState] using h_step

/-- On a nonsingular initial no-pivot Gram trajectory, any current state that is
ready for a regular next step has a nonzero previous pivot. -/
private theorem noPivotLoop_initial_gram_prevPivot_ne_zero_of_regular_prefix
    (b : Matrix Int n m) (fuel : Nat)
    (h_prefix_none :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none)
    (_hnext :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n)
    (_hp :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] ≠ 0) :
    (Matrix.noPivotLoop fuel
      (Matrix.noPivotInitialState (Matrix.gramMatrix b))).prevPivot ≠ 0 := by
  apply noPivotLoop_prevPivot_ne_zero_of_singularStep_none
  · simp [Matrix.noPivotInitialState]
  · exact h_prefix_none

/-- Package a proved zero suffix in the current Gram pivot column into the
executable row-pivot search failure expected by `Matrix.pivotLoop`. -/
private theorem noPivotLoop_initial_gram_findPivot?_eq_none_of_column_zero
    (b : Matrix Int n m) (s : Nat) (hs : s + 1 < n)
    (h_prefix_none :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none)
    (h_column_zero :
      ∀ i : Fin n, s + 1 ≤ i.val →
        (Matrix.noPivotLoop s
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][
          (⟨s, Nat.lt_of_succ_lt hs⟩ : Fin n)] = 0) :
    Matrix.findPivot?
        (Matrix.noPivotLoop s
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix
        (⟨s, Nat.lt_of_succ_lt hs⟩ : Fin n) (s + 1) = none := by
  have _h_step :=
    noPivotLoop_initial_gram_step_eq_of_prefix_none b s hs h_prefix_none
  exact Matrix.findPivot?_eq_none_of_zero _ _ _ h_column_zero

/-- After running `noPivotLoop fuel` from a state with `singularStep = none`, if
the result also has `singularStep = none`, then every column strictly between
the initial step and the final step is zero below the pivot in the final
matrix. Each such column was processed by a regular Bareiss step that cleared
its sub-diagonal entries, and no later iteration touches them. -/
private theorem noPivotLoop_matrix_processed_col_eq_zero {n : Nat} (fuel : Nat) :
    ∀ (state : Matrix.BareissState n),
      (Matrix.noPivotLoop fuel state).singularStep = none →
      ∀ (k : Nat), state.step ≤ k →
        k < (Matrix.noPivotLoop fuel state).step →
        ∀ (kFin : Fin n), kFin.val = k →
        ∀ (i : Fin n), k < i.val →
          (Matrix.noPivotLoop fuel state).matrix[i][kFin] = 0 := by
  induction fuel with
  | zero =>
      intros state _h_result k hk_ge hk_lt _kFin _hkFin i _hki
      simp [Matrix.noPivotLoop_zero_fuel] at hk_lt
      omega
  | succ f ih =>
      intros state h_result_none k hk_ge hk_lt kFin hkFin i hki
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · -- Singular branch contradicts h_result_none.
          rw [Matrix.noPivotLoop_singular_branch f state hDone hp] at h_result_none
          simp at h_result_none
        · -- Regular branch.
          let next : Matrix.BareissState n :=
            { step := state.step + 1
              matrix := Matrix.stepMatrix state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot
              prevPivot := state.matrix[state.step][state.step]
              rowSwaps := state.rowSwaps
              singularStep := none }
          have h_eq_next : Matrix.noPivotLoop (f + 1) state =
              Matrix.noPivotLoop f next :=
            Matrix.noPivotLoop_regular_branch f state hDone hp
          rw [h_eq_next] at h_result_none hk_lt ⊢
          by_cases hk_eq : k = state.step
          · -- k just got processed: column k was zeroed by stepMatrix.
            have hi_lt : state.step < i.val := hk_eq ▸ hki
            have hkFin_eq : kFin.val = state.step := hk_eq ▸ hkFin
            have h_next_zero : next.matrix[i][kFin] = 0 :=
              Matrix.stepMatrix_pivot_col_below state.matrix state.step
                state.matrix[state.step][state.step] state.prevPivot i kFin hi_lt hkFin_eq
            have h_fixed : kFin.val < next.step := by
              change kFin.val < state.step + 1
              omega
            have h_eq :=
              Matrix.noPivotLoop_matrix_entry_of_row_le_or_col_lt f next i kFin
                (Or.inr h_fixed)
            rw [h_eq]
            exact h_next_zero
          · -- k was processed at a later step inside `next`.
            have hk_ge_next : next.step ≤ k := by
              change state.step + 1 ≤ k
              omega
            exact ih next h_result_none k hk_ge_next hk_lt kFin hkFin i hki
      · -- Done branch: state.step unchanged, so hk_lt collapses.
        have h_eq_state : Matrix.noPivotLoop (f + 1) state = state :=
          Matrix.noPivotLoop_done f state hDone
        rw [h_eq_state] at h_result_none hk_lt ⊢
        omega

/-- Initial no-pivot Gram trajectory specialization of the regular row-entry
algebra.  The quotient package supplies the coefficient-side divisibility
provenance; the initial trajectory supplies nonzero `prevPivot` and the
already-processed column zeros needed by the one-step algebra. -/
private theorem bareissGramInitialRegularStep_entry_eq_dot
    (b : Matrix Int n m) (fuel : Nat)
    (hinv : BareissGramRowInvariant b
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))))
    (h_prefix_none :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none)
    (hnext :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n)
    (hp :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] ≠ 0)
    (i j : Fin n)
    (hi :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 ≤ i.val)
    (hq : BareissGramInitialRegularStepQuotient b fuel hinv hnext i hi) :
    (Matrix.stepMatrix
        (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix
        (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step
        (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
            (Matrix.noPivotLoop fuel
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
            (Matrix.noPivotLoop fuel
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step]
        (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).prevPivot)[i][j] =
      Matrix.dot
        (Matrix.rowCombination b
          (bareissGramRowInvariantStepCoeff hinv hnext i hi))
        (b.row j) := by
  let state :=
    Matrix.noPivotLoop fuel
      (Matrix.noPivotInitialState (Matrix.gramMatrix b))
  have hprev : state.prevPivot ≠ 0 :=
    noPivotLoop_initial_gram_prevPivot_ne_zero_of_regular_prefix
      b fuel h_prefix_none hnext hp
  have h_processed :
      ∀ i' : Fin n, state.step ≤ i'.val →
        ∀ j' : Fin n, j'.val < state.step → state.matrix[i'][j'] = 0 := by
    intro i' hi' j' hj'
    exact noPivotLoop_matrix_processed_col_eq_zero fuel
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)) h_prefix_none
      j'.val (by simp [Matrix.noPivotInitialState]) hj' j' rfl i'
      (Nat.lt_of_lt_of_le hj' hi')
  exact bareissGramRegularStep_entry_eq_dot hprev hq h_processed j

/-- Quotient provenance required to run the initial no-pivot Gram row invariant
through each reachable regular branch. -/
private abbrev BareissGramInitialRegularStepQuotientProvider
    (b : Matrix Int n m) : Type :=
  ∀ (fuel : Nat)
    (hinv : BareissGramRowInvariant b
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))))
    (h_prefix_none :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none)
    (hnext :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 < n)
    (_hp :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step][
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step] ≠ 0)
    (i : Fin n)
    (hi :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step + 1 ≤ i.val),
      BareissGramInitialRegularStepQuotient b fuel hinv hnext i hi

/-- Initial no-pivot Gram specialization indexed by elapsed fuel.  The regular
branch no longer asks callers for a row-entry equation; it obtains the
reachable row-entry relation from `bareissGramInitialRegularStep_entry_eq_dot`
using the supplied quotient provenance. -/
private def bareissGramRowInvariant_noPivotLoop_initialAux
    (b : Matrix Int n m) (elapsed fuel : Nat)
    (hinv : BareissGramRowInvariant b
      (Matrix.noPivotLoop elapsed
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))))
    (h_prefix_none :
      (Matrix.noPivotLoop elapsed
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none)
    (hquot : BareissGramInitialRegularStepQuotientProvider b) :
    BareissGramRowInvariant b
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotLoop elapsed
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)))) := by
  induction fuel generalizing elapsed with
  | zero =>
      simpa [Matrix.noPivotLoop_zero_fuel] using hinv
  | succ fuel ih =>
      let state :=
        Matrix.noPivotLoop elapsed
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))
      by_cases hDone : state.step + 1 < n
      · by_cases hp : state.matrix[state.step][state.step] = 0
        · rw [Matrix.noPivotLoop_singular_branch fuel state hDone hp]
          refine
            { coeff := hinv.coeff
              coeff_supp := ?_
              entry_eq_dot := ?_ }
          · simpa using hinv.coeff_supp
          · simpa using hinv.entry_eq_dot
        · rw [Matrix.noPivotLoop_regular_branch fuel state hDone hp]
          have hstep :
              Matrix.noPivotLoop (elapsed + 1)
                  (Matrix.noPivotInitialState (Matrix.gramMatrix b)) =
                ({ step := state.step + 1
                   matrix := Matrix.stepMatrix state.matrix state.step
                     state.matrix[state.step][state.step] state.prevPivot
                   prevPivot := state.matrix[state.step][state.step]
                   rowSwaps := state.rowSwaps
                   singularStep := none } : Matrix.BareissState n) := by
            rw [noPivotLoop_add elapsed 1
              (Matrix.noPivotInitialState (Matrix.gramMatrix b))]
            rw [Matrix.noPivotLoop_regular_branch 0 state hDone hp]
            simp [Matrix.noPivotLoop_zero_fuel]
          rw [← hstep]
          apply ih (elapsed := elapsed + 1)
          · rw [hstep]
            exact bareissGramRowInvariant_regular_step hDone hp hinv
              (fun i j hi =>
                bareissGramInitialRegularStep_entry_eq_dot
                  (b := b) elapsed hinv h_prefix_none hDone hp i j hi
                  (hquot elapsed hinv h_prefix_none hDone hp i hi))
          · rw [hstep]
      · rw [Matrix.noPivotLoop_done fuel state hDone]
        exact hinv

/-- Initial-state specialization of the row invariant for the no-pivot pass
over a Gram matrix.  Callers supply only quotient provenance for reachable
regular branches; the row-entry equation is derived internally. -/
private def bareissGramRowInvariant_noPivotLoop_initial
    (b : Matrix Int n m) (fuel : Nat)
    (hquot : BareissGramInitialRegularStepQuotientProvider b) :
    BareissGramRowInvariant b
      (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState (Matrix.gramMatrix b))) := by
  simpa using
    bareissGramRowInvariant_noPivotLoop_initialAux
      (b := b) 0 fuel (bareissGramRowInvariant_initial b) rfl hquot

/-- Caller-facing row-vector package for a no-pivot Gram pass from the
initial state. Downstream singular-step proofs can apply this at the loop
result to rewrite active trailing entries as dots against represented lattice
row vectors. -/
private theorem noPivotLoop_initial_gram_entry_eq_dot_of_rowInvariant
    (b : Matrix Int n m) (fuel : Nat)
    (hquot : BareissGramInitialRegularStepQuotientProvider b)
    (i j : Fin n)
    (hi :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step ≤ i.val) :
    ∃ v : Vector Int m,
      (∃ c : Vector Int n,
        (∀ k : Fin n, i.val < k.val → c[k] = 0) ∧
          v = Matrix.rowCombination b c) ∧
        (Matrix.noPivotLoop fuel
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][j] =
          Matrix.dot v (b.row j) := by
  exact bareissGramRowInvariant_exists_rowVec
    (bareissGramRowInvariant_noPivotLoop_initial b fuel hquot) i j hi

/-- Row-vector consumer for an initial no-pivot Gram pass.  A single supported
integer row combination represents the active row `i` against every original
input row, so downstream singular-column arguments do not need to inspect
`BareissGramRowInvariant` or supply the generic regular-branch row-entry
equation. -/
private theorem noPivotLoop_initial_gram_exists_rowVec
    (b : Matrix Int n m) (fuel : Nat)
    (hquot : BareissGramInitialRegularStepQuotientProvider b)
    (i : Fin n)
    (hi :
      (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step ≤ i.val) :
    ∃ v : Vector Int m,
      (∃ c : Vector Int n,
        (∀ k : Fin n, i.val < k.val → c[k] = 0) ∧
          v = Matrix.rowCombination b c) ∧
        ∀ j : Fin n,
          (Matrix.noPivotLoop fuel
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][j] =
            Matrix.dot v (b.row j) := by
  let hinv :=
    bareissGramRowInvariant_noPivotLoop_initial b fuel hquot
  refine ⟨Matrix.rowCombination b (hinv.coeff i), ?_, ?_⟩
  · exact ⟨hinv.coeff i, fun k hik => hinv.coeff_supp i k hi hik, rfl⟩
  · intro j
    exact hinv.entry_eq_dot i j hi

private theorem int_mul_self_nonneg (x : Int) : 0 ≤ x * x := by
  simpa [Lean.Grind.Semiring.pow_two] using
    (Lean.Grind.OrderedRing.sq_nonneg (a := x))

private theorem int_mul_self_eq_zero_of_nonpos (x : Int) (h : x * x ≤ 0) : x = 0 := by
  have hnonneg : 0 ≤ x * x := int_mul_self_nonneg x
  have hsquare : x * x = 0 := Int.le_antisymm h hnonneg
  rcases Int.mul_eq_zero.mp hsquare with h0 | h0 <;> exact h0

private theorem foldl_int_dot_self_start_le (xs : List (Fin m)) (v : Vector Int m)
    (acc : Int) (hacc : 0 ≤ acc) :
    acc ≤ xs.foldl (fun sum i => sum + v[i] * v[i]) acc := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hsq : 0 ≤ v[i] * v[i] := int_mul_self_nonneg v[i]
      have hnext : 0 ≤ acc + v[i] * v[i] := by grind
      exact Int.le_trans (by grind) (ih (acc := acc + v[i] * v[i]) hnext)

private theorem foldl_int_dot_self_eq_zero_of_mem (xs : List (Fin m))
    (v : Vector Int m) (acc : Int) (hacc : 0 ≤ acc)
    (hzero : xs.foldl (fun sum i => sum + v[i] * v[i]) acc = 0) :
    ∀ i ∈ xs, v[i] = 0 := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons head rest ih =>
      intro i hi
      simp only [List.mem_cons] at hi
      have hsq : 0 ≤ v[head] * v[head] := int_mul_self_nonneg v[head]
      have hnext_nonneg : 0 ≤ acc + v[head] * v[head] := by grind
      have hnext_le_zero : acc + v[head] * v[head] ≤ 0 := by
        have hle :=
          foldl_int_dot_self_start_le (xs := rest) (v := v)
            (acc := acc + v[head] * v[head]) hnext_nonneg
        have hzero' :
            rest.foldl (fun sum i => sum + v[i] * v[i])
              (acc + v[head] * v[head]) = 0 := by
          simpa using hzero
        rw [hzero'] at hle
        exact hle
      have hnext_zero : acc + v[head] * v[head] = 0 := by grind
      have hhead_zero : v[head] = 0 := by
        apply int_mul_self_eq_zero_of_nonpos
        grind
      cases hi with
      | inl h =>
          subst i
          exact hhead_zero
      | inr h =>
          exact ih (acc := acc + v[head] * v[head]) hnext_nonneg hzero i h

private theorem int_dot_self_eq_zero_get (v : Vector Int m)
    (hzero : Matrix.dot v v = 0) (i : Fin m) :
    v[i] = 0 := by
  have hmem : i ∈ List.finRange m := by simp
  exact foldl_int_dot_self_eq_zero_of_mem (xs := List.finRange m) (v := v)
    (acc := 0) (by decide)
    (by simpa [Matrix.dot, Hex.Vector.dotProduct] using hzero) i hmem

/-- An integer vector whose self-dot product is zero is itself the zero vector.
A finite-dimensional positive-definiteness fact for `Vector Int m`. -/
private theorem int_vector_eq_zero_of_dot_self_zero (v : Vector Int m)
    (hzero : Matrix.dot v v = 0) :
    v = Vector.ofFn fun _ : Fin m => (0 : Int) := by
  apply Vector.ext
  intro i hi
  rw [Vector.getElem_ofFn]
  exact int_dot_self_eq_zero_get v hzero ⟨i, hi⟩

/-- If `v : Vector Int m` has zero self-dot product, then its dot product
against any other integer vector is zero. -/
private theorem int_dot_eq_zero_of_dot_self_zero (u v : Vector Int m)
    (hzero : Matrix.dot v v = 0) :
    Matrix.dot u v = 0 := by
  unfold Matrix.dot Hex.Vector.dotProduct
  induction List.finRange m with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [int_dot_self_eq_zero_get v hzero i]
      have hzero_mul : u[i] * (0 : Int) = 0 := by grind
      rw [hzero_mul]
      have hadd_zero : (0 : Int) + 0 = 0 := by grind
      rw [hadd_zero]
      exact ih

/-- If `v : Vector Int m` has zero self-dot product, then any other integer
vector dots it to zero from the left as well. -/
private theorem int_dot_eq_zero_of_dot_self_zero_left (u v : Vector Int m)
    (hzero : Matrix.dot v v = 0) :
    Matrix.dot v u = 0 := by
  unfold Matrix.dot Hex.Vector.dotProduct
  induction List.finRange m with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [int_dot_self_eq_zero_get v hzero i]
      have hzero_mul : (0 : Int) * u[i] = 0 := by grind
      rw [hzero_mul]
      have hadd_zero : (0 : Int) + 0 = 0 := by grind
      rw [hadd_zero]
      exact ih

private theorem foldl_dot_comm_int_local {n' : Nat} (xs : List (Fin n'))
    (u v : Vector Int n') (accU accV : Int) (hacc : accU = accV) :
    xs.foldl (fun acc i => acc + u[i] * v[i]) accU =
      xs.foldl (fun acc i => acc + v[i] * u[i]) accV := by
  induction xs generalizing accU accV with
  | nil =>
      simp [hacc]
  | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih
      grind

/-- The dot product of integer vectors is commutative. (Local form for use
inside this file before the existing `dot_comm_int` declaration.) -/
private theorem int_dot_comm_local {n' : Nat} (u v : Vector Int n') :
    Matrix.dot u v = Matrix.dot v u := by
  simpa [Matrix.dot, Hex.Vector.dotProduct] using
    foldl_dot_comm_int_local (xs := List.finRange n') (u := u) (v := v)
      (accU := 0) (accV := 0) rfl

/-- Pointwise function equality for foldl-style sums lifts to a foldl equality. -/
private theorem foldl_add_pointwise_eq_int {α : Type v}
    (xs : List α) (f g : α → Int) (acc : Int)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.foldl (fun acc x => acc + f x) acc =
      xs.foldl (fun acc x => acc + g x) acc := by
  induction xs generalizing acc with
  | nil =>
      rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = g x := h x (by simp)
      have hxs : ∀ y ∈ xs, f y = g y :=
        fun y hy => h y (List.mem_cons_of_mem _ hy)
      rw [hx]
      exact ih (acc + g x) hxs

/-- Entry-level formula for `rowCombination` over integers: the `j`th entry is
the sum over `k` of `b[k][j] * c[k]`. -/
private theorem rowCombination_getElem_int
    {n m : Nat} (b : Matrix Int n m) (c : Vector Int n) (j : Fin m) :
    (Matrix.rowCombination b c)[j] =
      (List.finRange n).foldl (fun acc k => acc + b[k][j] * c[k]) 0 := by
  show (Matrix.transpose b * c)[j] = _
  rw [Matrix.mulVec_getElem]
  unfold Matrix.dot Hex.Vector.dotProduct
  apply foldl_add_pointwise_eq_int
  intro k _hk
  simp [Matrix.transpose, Matrix.col, Matrix.row]

/-- Distribute a constant `x : Int` through a foldl-style sum body. -/
private theorem foldl_mul_distrib_int {α : Type v}
    (xs : List α) (f : α → Int) (x acc : Int) :
    x * xs.foldl (fun acc y => acc + f y) acc =
      xs.foldl (fun acc y => acc + x * f y) (x * acc) := by
  induction xs generalizing acc with
  | nil => simp
  | cons y rest ih =>
      simp only [List.foldl_cons]
      rw [ih (acc + f y)]
      have : x * (acc + f y) = x * acc + x * f y := by grind
      rw [this]

/-- Expansion of the dot product against `rowCombination` over integers: the
second argument's row combination distributes outside the sum, giving the
Σ-over-rows form. Proved via the `Hex.Matrix.foldl_det_sum_swap` Fubini
identity. -/
private theorem dot_rowCombination_right_eq_foldl_int
    {n m : Nat} (b : Matrix Int n m) (u : Vector Int m) (c : Vector Int n) :
    Matrix.dot u (Matrix.rowCombination b c) =
      (List.finRange n).foldl
        (fun acc k => acc + c[k] * Matrix.dot u (b.row k)) 0 := by
  -- Step 1: rewrite each (rowComb b c)[j] entry using rowCombination_getElem_int.
  have h_lhs :
      Matrix.dot u (Matrix.rowCombination b c) =
        (List.finRange m).foldl
          (fun accj j => accj + u[j] *
            (List.finRange n).foldl (fun acck k => acck + b[k][j] * c[k]) 0) 0 := by
    unfold Matrix.dot Hex.Vector.dotProduct
    apply foldl_add_pointwise_eq_int
    intro j _hj
    rw [rowCombination_getElem_int (b := b) (c := c) j]
  rw [h_lhs]
  -- Step 2: distribute u[j] over the inner sum so the body has shape (acc + f j k).
  have h_distrib :
      (List.finRange m).foldl
          (fun accj j => accj + u[j] *
            (List.finRange n).foldl (fun acck k => acck + b[k][j] * c[k]) 0) 0 =
        (List.finRange m).foldl
          (fun accj j => accj +
            (List.finRange n).foldl
              (fun acck k => acck + u[j] * (b[k][j] * c[k])) 0) 0 := by
    apply foldl_add_pointwise_eq_int
    intro j _hj
    have h_mul := foldl_mul_distrib_int (List.finRange n)
      (fun k : Fin n => b[k][j] * c[k]) u[j] 0
    have h_zero : u[j] * (0 : Int) = 0 := by grind
    rw [h_zero] at h_mul
    exact h_mul
  rw [h_distrib]
  -- Step 3: apply Fubini sum-swap.
  have h_swap :=
    Matrix.foldl_det_sum_swap (R := Int)
      (xs := List.finRange m) (ys := List.finRange n)
      (fun (j : Fin m) (k : Fin n) => u[j] * (b[k][j] * c[k]))
  rw [h_swap]
  -- Step 4: reshape each inner sum to match c[k] * dot u (b.row k).
  apply foldl_add_pointwise_eq_int
  intro k _hk
  -- We want:
  --   (List.finRange m).foldl (fun accj j => accj + u[j] * (b[k][j] * c[k])) 0
  --     = c[k] * Matrix.dot u (b.row k)
  -- Rearrange body so c[k] is the multiplier: u[j] * (b[k][j] * c[k])
  --     = c[k] * (u[j] * b[k][j]).
  have h_body :
      (List.finRange m).foldl
          (fun accj j => accj + u[j] * (b[k][j] * c[k])) 0 =
        (List.finRange m).foldl
          (fun accj j => accj + c[k] * (u[j] * b[k][j])) 0 := by
    apply foldl_add_pointwise_eq_int
    intro j _hj
    have : u[j] * (b[k][j] * c[k]) = c[k] * (u[j] * b[k][j]) := by grind
    exact this
  rw [h_body]
  -- Pull c[k] out of the foldl using foldl_mul_distrib_int (in reverse).
  have h_pull := foldl_mul_distrib_int (List.finRange m)
    (fun j : Fin m => u[j] * b[k][j]) c[k] 0
  have h_zero : c[k] * (0 : Int) = 0 := by grind
  rw [h_zero] at h_pull
  rw [← h_pull]
  -- Goal: c[k] * (List.finRange m).foldl (fun accj j => accj + u[j] * b[k][j]) 0
  --      = c[k] * Matrix.dot u (b.row k)
  -- Rewrite Matrix.dot definitionally to the foldl form using row entry equality.
  have h_dot_eq :
      Matrix.dot u (b.row k) =
        (List.finRange m).foldl (fun accj j => accj + u[j] * b[k][j]) 0 := by
    unfold Matrix.dot Hex.Vector.dotProduct
    apply foldl_add_pointwise_eq_int
    intro j _hj
    simp [Matrix.row]
  rw [h_dot_eq]

/-- A foldl-style sum whose every term is zero starting from a zero accumulator
collapses to zero. -/
private theorem foldl_add_zero_of_terms_zero_int {α : Type v}
    (xs : List α) (f : α → Int)
    (h : ∀ x ∈ xs, f x = 0) :
    xs.foldl (fun acc x => acc + f x) (0 : Int) = 0 := by
  have h_aux : ∀ (xs : List α) (acc : Int),
      (∀ x ∈ xs, f x = 0) →
        xs.foldl (fun acc x => acc + f x) acc = acc := by
    intro xs
    induction xs with
    | nil => intros acc _h; rfl
    | cons y rest ih =>
        intros acc h_terms
        simp only [List.foldl_cons]
        have hy : f y = 0 := h_terms y (by simp)
        have hxs : ∀ x ∈ rest, f x = 0 :=
          fun x hx => h_terms x (List.mem_cons_of_mem _ hx)
        rw [hy]
        have h_add : acc + (0 : Int) = acc := by grind
        rw [h_add]
        exact ih (acc) hxs
  exact h_aux xs 0 h

/-- Gram zero-pivot column suffix: if the no-pivot Bareiss pass over the Gram
matrix runs `s` steps without recording a singular step but the pivot entry
`matrix[s][s]` is zero, then every later row's entry in column `s` is zero
too. This is the `h_column_zero` premise consumed by
`noPivotLoop_initial_gram_findPivot?_eq_none_of_column_zero` to discharge the
executable `findPivot? = none` form needed by the row-pivoted Bareiss loop on
the Gram trajectory.

The argument: by the closed row-vector consumer, the represented pivot row has
integer support on indices `≤ s` and inner product zero against `b.row k` for
every `k.val ≤ s` (those matrix entries are either the zero pivot itself or
zeros left by earlier regular elimination steps). Linearity of dot against
`rowCombination` over the supported indices then gives `Matrix.dot v v = 0`,
and integer positive definiteness forces every dot against `v` to be zero.
Trailing-block symmetry transports
`state.matrix[sFin][i] = Matrix.dot v (b.row i) = 0` across the diagonal to
`state.matrix[i][sFin] = 0`. -/
private theorem leadingPrefix_gram_zero_pivot_column_zero_of_singular_step
    {n m : Nat} (b : Matrix Int n m) (s : Nat) (hs : s + 1 < n)
    (hquot : BareissGramInitialRegularStepQuotientProvider b)
    (h_prefix_none :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none)
    (h_zero :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[
          (⟨s, Nat.lt_of_succ_lt hs⟩ : Fin n)][
          (⟨s, Nat.lt_of_succ_lt hs⟩ : Fin n)] = 0) :
    ∀ i : Fin n, s + 1 ≤ i.val →
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][
          (⟨s, Nat.lt_of_succ_lt hs⟩ : Fin n)] = 0 := by
  intro i hi
  let sFin : Fin n := ⟨s, Nat.lt_of_succ_lt hs⟩
  -- Final state of the loop and its `step = s` alignment.
  have h_step :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step = s :=
    noPivotLoop_initial_gram_step_eq_of_prefix_none b s hs h_prefix_none
  have h_state_step_le_sFin :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step ≤ sFin.val := by
    rw [h_step]; show s ≤ s; exact Nat.le_refl _
  -- The row-vector consumer aligns `matrix[sFin][j]` with
  -- `Matrix.dot v (b.row j)` for all columns `j`.
  obtain ⟨v, ⟨c, h_coeff_supp_above, hv_def⟩, h_dot_eq_matrix⟩ :=
    noPivotLoop_initial_gram_exists_rowVec b s hquot sFin h_state_step_le_sFin
  -- The represented row is orthogonal to `b.row k` for every `k.val ≤ s`:
  -- on `k.val = s`, the hypothesis `h_zero` gives a zero pivot dot, and on
  -- `k.val < s` the column was cleared by an earlier regular Bareiss step.
  have h_dot_zero_le : ∀ k : Fin n, k.val ≤ s →
      Matrix.dot v (b.row k) = 0 := by
    intro k hks
    rw [← h_dot_eq_matrix k]
    by_cases hk_eq : k.val = s
    · have h_k_eq_sFin : k = sFin := Fin.ext hk_eq
      rw [h_k_eq_sFin]
      exact h_zero
    · -- k.val < s, use column-zero helper at fuel = s, k as kFin, sFin as i.
      have hk_lt : k.val < s := Nat.lt_of_le_of_ne hks hk_eq
      have h_init_step_le :
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step ≤ k.val := by
        show 0 ≤ k.val
        exact Nat.zero_le _
      have h_k_lt_result :
          k.val < (Matrix.noPivotLoop s
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).step := by
        rw [h_step]
        exact hk_lt
      have h_k_lt_sFin : k.val < sFin.val := hk_lt
      exact noPivotLoop_matrix_processed_col_eq_zero s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)) h_prefix_none
        k.val h_init_step_le h_k_lt_result k rfl sFin h_k_lt_sFin
  -- `Matrix.dot v v = 0`: every term in the rowCombination expansion is zero.
  have h_dot_self_zero : Matrix.dot v v = 0 := by
    have h_expand_aux :
        Matrix.dot v (Matrix.rowCombination b c) =
          (List.finRange n).foldl
            (fun acc k => acc + c[k] * Matrix.dot v (b.row k))
            0 :=
      dot_rowCombination_right_eq_foldl_int b v c
    rw [← hv_def] at h_expand_aux
    rw [h_expand_aux]
    apply foldl_add_zero_of_terms_zero_int
    intro k _hk
    by_cases hks : k.val ≤ s
    · -- second factor is zero
      rw [h_dot_zero_le k hks]
      grind
    · -- first factor is zero
      have hk_gt : sFin.val < k.val := by show s < k.val; omega
      rw [h_coeff_supp_above k hk_gt]
      grind
  -- Transport across symmetry: `matrix[i][sFin] = matrix[sFin][i]`.
  have h_init_sym :
      ∀ a c : Fin n,
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step ≤ a.val →
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step ≤ c.val →
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)).matrix[a][c] =
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)).matrix[c][a] := by
    intros a c _ha _hc
    show (Matrix.gramMatrix b)[a][c] = (Matrix.gramMatrix b)[c][a]
    rw [Matrix.gramMatrix_getElem, Matrix.gramMatrix_getElem]
    exact int_dot_comm_local (Matrix.row b a) (Matrix.row b c)
  have h_symm :
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][sFin] =
      (Matrix.noPivotLoop s
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[sFin][i] := by
    apply noPivotLoop_matrix_symm_preserve s
      (Matrix.noPivotInitialState (Matrix.gramMatrix b)) h_init_sym i sFin
    · rw [h_step]; omega
    · rw [h_step]; show s ≤ s; exact Nat.le_refl _
  -- Now matrix[sFin][i] = dot v (b.row i) = 0 via integer positive definiteness.
  rw [h_symm, h_dot_eq_matrix i]
  exact int_dot_eq_zero_of_dot_self_zero_left (b.row i) v h_dot_self_zero

/-- Substitution helper for the diagonal `(i, i)` matrix entry under a Fin
equality. -/
private theorem matrix_diag_at_fin_eq {n : Nat} (M : Matrix Int n n)
    {i j : Fin n} (h : i = j) :
    M[i][i] = M[j][j] := by
  subst h; rfl

/-- If the `a`-fueled no-pivot Bareiss prefix already recorded a singular step,
that step persists into any longer pass. -/
private theorem noPivotLoop_extends_singularStep
    {n : Nat} (state : Matrix.BareissState n) (a b : Nat) (k : Fin n)
    (h_sing_a : (Matrix.noPivotLoop a state).singularStep = some k.val)
    (h_step_a : (Matrix.noPivotLoop a state).step = k.val)
    (h_zero_a : (Matrix.noPivotLoop a state).matrix[k][k] = 0)
    (hk : k.val + 1 < n) :
    Matrix.noPivotLoop (a + b) state = Matrix.noPivotLoop a state := by
  rw [Matrix.noPivotLoop_add a b state]
  have hDone : (Matrix.noPivotLoop a state).step + 1 < n := by
    rw [h_step_a]; exact hk
  have hp_zero :
      (Matrix.noPivotLoop a state).matrix[
        (⟨(Matrix.noPivotLoop a state).step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
        (⟨(Matrix.noPivotLoop a state).step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0 := by
    have h_fin :
        (⟨(Matrix.noPivotLoop a state).step, Nat.lt_of_succ_lt hDone⟩ : Fin n) = k :=
      Fin.ext h_step_a
    exact (matrix_diag_at_fin_eq (Matrix.noPivotLoop a state).matrix h_fin).trans h_zero_a
  have h_sing_step : (Matrix.noPivotLoop a state).singularStep =
      some (Matrix.noPivotLoop a state).step := by
    rw [h_sing_a, h_step_a]
  exact Matrix.noPivotLoop_id_at_singular_fixedpoint (n := n) b
    (Matrix.noPivotLoop a state) hDone hp_zero h_sing_step

/-- From a partial no-pivot Bareiss pass on `M` recording a singular step at
index `s`, derive that the `s`-fueled prefix is non-singular, has reached
`step = s`, and has zero diagonal at `(s, s)`. -/
private theorem noPivotLoop_prefix_state_at_singular
    {n : Nat} (M : Matrix Int n n) (fuel s : Nat) (hs : s + 1 ≤ n)
    (h_sing : (Matrix.noPivotLoop fuel
        (Matrix.noPivotInitialState M)).singularStep = some s) :
    (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).singularStep = none ∧
      (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).step = s ∧
      (Matrix.noPivotLoop s
          (Matrix.noPivotInitialState M)).matrix[
            (⟨s, Nat.lt_of_succ_le hs⟩ : Fin n)][
            (⟨s, Nat.lt_of_succ_le hs⟩ : Fin n)] = 0 := by
  have h_init_sing : (Matrix.noPivotInitialState M).singularStep = none := rfl
  have h_init_step : (Matrix.noPivotInitialState M).step = 0 := rfl
  have hsfuel : s < fuel := by
    have := noPivotLoop_singularStep_lt (n := n) fuel
      (Matrix.noPivotInitialState M) h_init_sing s h_sing
    rw [h_init_step] at this
    omega
  rcases noPivotLoop_singular_inv (n := n) s
      (Matrix.noPivotInitialState M) h_init_sing
    with h_none | ⟨k', h_sing_s, h_step_s, h_zero_s, h_klt⟩
  · have hS_step : (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).step = s := by
      have h_room :
          (Matrix.noPivotInitialState M).step + s + 1 ≤ n := by
        rw [h_init_step]; omega
      have h_step := Matrix.noPivotLoop_step_eq_add_of_singularStep_none
        (n := n) s (Matrix.noPivotInitialState M) h_init_sing h_room h_none
      rw [h_step, h_init_step]; omega
    refine ⟨h_none, hS_step, ?_⟩
    rcases noPivotLoop_singular_inv (n := n) fuel
        (Matrix.noPivotInitialState M) h_init_sing
      with h_full_none | ⟨k, h_sing_full, h_step_full, h_zero_full, h_klt_full⟩
    · rw [h_full_none] at h_sing; nomatch h_sing
    · have hk_eq : k.val = s := by
        rw [h_sing_full] at h_sing
        exact Option.some.inj h_sing
      have hsn : s < n := Nat.lt_of_succ_le hs
      have h_full_eq :
          Matrix.noPivotLoop (s + (fuel - s)) (Matrix.noPivotInitialState M) =
            Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M) := by
        congr 1; omega
      have h_split :
          Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M) =
            Matrix.noPivotLoop (fuel - s)
              (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)) := by
        rw [← h_full_eq,
          Matrix.noPivotLoop_add s (fuel - s) (Matrix.noPivotInitialState M)]
      have h_diag_preserved :
          (Matrix.noPivotLoop (fuel - s)
              (Matrix.noPivotLoop s (Matrix.noPivotInitialState M))).matrix[
              (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] =
            (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).matrix[
              (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] :=
        Matrix.noPivotLoop_diag_of_le_step (fuel - s)
          (Matrix.noPivotLoop s (Matrix.noPivotInitialState M))
          (⟨s, hsn⟩ : Fin n)
          (by rw [hS_step]; exact Nat.le_refl _)
      have h_full_diag_eq :
          (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M)).matrix[
              (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] =
            (Matrix.noPivotLoop s (Matrix.noPivotInitialState M)).matrix[
              (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] := by
        rw [h_split]; exact h_diag_preserved
      have h_fin : k = (⟨s, hsn⟩ : Fin n) := Fin.ext hk_eq
      have h_full_zero :
          (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M)).matrix[
            (⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] = 0 :=
        (matrix_diag_at_fin_eq
            (Matrix.noPivotLoop fuel (Matrix.noPivotInitialState M)).matrix h_fin).symm.trans
          h_zero_full
      exact h_full_diag_eq.symm.trans h_full_zero
  · have h_klt' : k'.val < s := by
      have := noPivotLoop_singularStep_lt (n := n) s
        (Matrix.noPivotInitialState M) h_init_sing k'.val h_sing_s
      rw [h_init_step] at this
      omega
    have h_persist :
        Matrix.noPivotLoop (s + (fuel - s)) (Matrix.noPivotInitialState M) =
          Matrix.noPivotLoop s (Matrix.noPivotInitialState M) :=
      noPivotLoop_extends_singularStep (Matrix.noPivotInitialState M) s (fuel - s) k'
        h_sing_s h_step_s h_zero_s h_klt
    have h_fuel_eq : s + (fuel - s) = fuel := by omega
    rw [h_fuel_eq] at h_persist
    rw [h_persist] at h_sing
    rw [h_sing_s] at h_sing
    have hk'_eq : k'.val = s := Option.some.inj h_sing
    omega

/-- If the row-pivoted Bareiss loop is in a state where, after `a` regular
no-pivot iterations, the next pivot is zero and the column has no replacement,
the loop records the resulting step as singular regardless of any remaining
fuel beyond the triggering iteration. The partial-pass result is passed
explicitly as `result` to keep Fin-index proof terms uniform across the
induction. -/
private theorem pivotLoop_singularStep_some_of_partial_no_replacement
    {n : Nat} :
    ∀ (a : Nat) (fuel : Nat) (state : Matrix.BareissState n)
      (result : Matrix.BareissState n)
      (h_partial : Matrix.noPivotLoop a state = result),
      state.singularStep = none →
      a + 1 ≤ fuel →
      result.singularStep = none →
      (h_step_lt : result.step + 1 < n) →
      result.matrix[(⟨result.step, Nat.lt_of_succ_lt h_step_lt⟩ : Fin n)][
        (⟨result.step, Nat.lt_of_succ_lt h_step_lt⟩ : Fin n)] = 0 →
      Matrix.findPivot? result.matrix
        (⟨result.step, Nat.lt_of_succ_lt h_step_lt⟩ : Fin n) (result.step + 1) = none →
      (Matrix.pivotLoop fuel state).singularStep = some result.step := by
  intro a
  induction a with
  | zero =>
      intro fuel state result h_partial _h_init_sing hfuel _h_part_none hStepLt hp_zero
          h_find_none
      -- noPivotLoop 0 state = state.
      have h_state_eq : state = result := by
        rw [show state = Matrix.noPivotLoop 0 state from rfl, h_partial]
      subst h_state_eq
      rcases fuel with _ | fuel'
      · omega
      exact (Matrix.pivotLoop_singular_branch_no_pivot fuel' state hStepLt hp_zero h_find_none
        ▸ rfl)
  | succ a' ih =>
      intro fuel state result h_partial h_init_sing hfuel h_part_none hStepLt hp_zero
          h_find_none
      have hDone_state : state.step + 1 < n := by
        have hmono := noPivotLoop_step_monotone (a' + 1) state
        rw [h_partial] at hmono
        omega
      by_cases hp0_state : state.matrix[state.step][state.step] = 0
      · -- Singular first iteration contradicts result.singularStep = none.
        exfalso
        have h_sing_branch :
            Matrix.noPivotLoop (a' + 1) state =
              { state with singularStep := some state.step } :=
          Matrix.noPivotLoop_singular_branch a' state hDone_state hp0_state
        rw [h_sing_branch] at h_partial
        rw [← h_partial] at h_part_none
        simp at h_part_none
      · -- Regular first iteration: recurse on the updated state.
        have h_unfold_noPiv : Matrix.noPivotLoop (a' + 1) state =
            Matrix.noPivotLoop a'
              { step := state.step + 1
                matrix := Matrix.stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot
                prevPivot := state.matrix[state.step][state.step]
                rowSwaps := state.rowSwaps
                singularStep := none } :=
          Matrix.noPivotLoop_regular_branch a' state hDone_state hp0_state
        rcases fuel with _ | fuel'
        · omega
        have h_fuel' : a' + 1 ≤ fuel' := by omega
        have h_unfold_piv : Matrix.pivotLoop (fuel' + 1) state =
            Matrix.pivotLoop fuel'
              { step := state.step + 1
                matrix := Matrix.stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot
                prevPivot := state.matrix[state.step][state.step]
                rowSwaps := state.rowSwaps
                singularStep := none } :=
          Matrix.pivotLoop_regular_branch_no_swap fuel' state hDone_state hp0_state
        rw [h_unfold_piv]
        have h_next_partial :
            Matrix.noPivotLoop a'
              ({ step := state.step + 1
                 matrix := Matrix.stepMatrix state.matrix state.step
                   state.matrix[state.step][state.step] state.prevPivot
                 prevPivot := state.matrix[state.step][state.step]
                 rowSwaps := state.rowSwaps
                 singularStep := none } : Matrix.BareissState n) = result := by
          rw [← h_unfold_noPiv]; exact h_partial
        exact ih fuel'
          { step := state.step + 1
            matrix := Matrix.stepMatrix state.matrix state.step
              state.matrix[state.step][state.step] state.prevPivot
            prevPivot := state.matrix[state.step][state.step]
            rowSwaps := state.rowSwaps
            singularStep := none }
          result h_next_partial rfl h_fuel' h_part_none hStepLt hp_zero h_find_none

/-- Singular branch of the Gram leading-prefix Bareiss identification: if the
no-pivot Bareiss pass over the full Gram matrix records a singular step at index
`s` strictly before slot `r + 1`, the public row-pivoted Bareiss determinant of
the `(r + 1)` leading Gram prefix is `Nat.zero`. The proof translates the
column-zero suffix from the closed row invariant on the full trajectory to the
leading prefix via the no-pivot sync lemma, then derives `findPivot? = none` on
the prefix, so the row-pivoted Bareiss loop records the same singular step. -/
private theorem leadingPrefix_gram_bareiss_toNat_eq_zero_of_noPivot_singular
    {n m : Nat} (b : Matrix Int n m) (r : Nat) (hr : r < n)
    (hquot : BareissGramInitialRegularStepQuotientProvider b)
    (s : Nat)
    (h_sing : (Matrix.noPivotLoop r
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s) :
    (Matrix.bareiss
      (Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1)
        (Nat.succ_le_of_lt hr))).toNat = 0 := by
  let GM := Matrix.gramMatrix b
  let initGM := Matrix.noPivotInitialState GM
  let hK : r + 1 ≤ n := Nat.succ_le_of_lt hr
  let LP := Matrix.leadingPrefix GM (r + 1) hK
  let initLP := Matrix.noPivotInitialState LP
  -- Step 1: s < r via noPivotLoop_singularStep_lt.
  have hsr : s < r := by
    have h := noPivotLoop_singularStep_lt (n := n) r initGM rfl s h_sing
    change s < initGM.step + r at h
    have : initGM.step = 0 := rfl
    omega
  have hs1n : s + 1 < n := Nat.lt_of_lt_of_le (Nat.succ_lt_succ hsr) hr
  have hsn : s < n := Nat.lt_of_succ_lt hs1n
  -- Step 2: extract partial state at s iterations.
  have hsucc_n : s + 1 ≤ n := Nat.le_of_lt hs1n
  obtain ⟨h_full_none, h_full_step, h_full_zero⟩ :=
    noPivotLoop_prefix_state_at_singular GM r s hsucc_n h_sing
  -- Step 3: column-zero on FULL via leadingPrefix_gram_zero_pivot_column_zero_of_singular_step.
  have h_full_col_zero :
      ∀ i : Fin n, s + 1 ≤ i.val →
        (Matrix.noPivotLoop s initGM).matrix[i][(⟨s, hsn⟩ : Fin n)] = 0 :=
    leadingPrefix_gram_zero_pivot_column_zero_of_singular_step
      (b := b) s hs1n hquot h_full_none h_full_zero
  -- Step 4: sync — leadingPrefix (noPivotLoop s initGM).matrix (r+1) = (noPivotLoop s initLP).matrix.
  have h_sync :=
    noPivotLoop_sync_leadingPrefix_aux (n := n) (K := r + 1) hK s
      initGM initLP rfl rfl rfl rfl
      (by
        show Matrix.leadingPrefix initGM.matrix (r + 1) hK = initLP.matrix
        rfl)
      (show s + initGM.step < r + 1 by
        change s + 0 < r + 1; omega)
  obtain ⟨h_step_sync, _h_prev_sync, _h_rows_sync, h_sing_sync, h_mat_sync⟩ := h_sync
  -- Useful Fin bound.
  have hs_lt_r1 : s < r + 1 := Nat.lt_succ_of_lt hsr
  -- Step 5: translate column-zero to LP.
  have h_LP_col_zero :
      ∀ i' : Fin (r + 1), s + 1 ≤ i'.val →
        (Matrix.noPivotLoop s initLP).matrix[i'][
          (⟨s, hs_lt_r1⟩ : Fin (r + 1))] = 0 := by
    intro i' hi'
    let iN : Fin n := ⟨i'.val, Nat.lt_of_lt_of_le i'.isLt hK⟩
    have h_LP_entry :
        (Matrix.noPivotLoop s initLP).matrix[i'][
          (⟨s, hs_lt_r1⟩ : Fin (r + 1))] =
        (Matrix.leadingPrefix (Matrix.noPivotLoop s initGM).matrix (r + 1) hK)[i'][
          (⟨s, hs_lt_r1⟩ : Fin (r + 1))] := by
      rw [← h_mat_sync]
    rw [h_LP_entry]
    rw [Matrix.leadingPrefix_entry (Matrix.noPivotLoop s initGM).matrix (r + 1) hK i'
      (⟨s, hs_lt_r1⟩ : Fin (r + 1))]
    have hi_iN : s + 1 ≤ iN.val := hi'
    have h_col_zero_iN := h_full_col_zero iN hi_iN
    have h_entry_eq :
        (Matrix.noPivotLoop s initGM).matrix[iN][
          (⟨s, Nat.lt_of_lt_of_le hs_lt_r1 hK⟩ : Fin n)] =
        (Matrix.noPivotLoop s initGM).matrix[iN][(⟨s, hsn⟩ : Fin n)] :=
      congrArg (fun (j : Fin n) => (Matrix.noPivotLoop s initGM).matrix[iN][j])
        (Fin.ext (rfl : (⟨s, Nat.lt_of_lt_of_le hs_lt_r1 hK⟩ : Fin n).val =
                        (⟨s, hsn⟩ : Fin n).val))
    exact h_entry_eq.trans h_col_zero_iN
  -- Step 6: findPivot? = none on LP.
  have h_LP_step : (Matrix.noPivotLoop s initLP).step = s := by
    rw [← h_step_sync]; exact h_full_step
  have h_LP_sing : (Matrix.noPivotLoop s initLP).singularStep = none := by
    rw [← h_sing_sync]; exact h_full_none
  have h_LP_zero_diag :
      (Matrix.noPivotLoop s initLP).matrix[(⟨s, hs_lt_r1⟩ : Fin (r + 1))][
        (⟨s, hs_lt_r1⟩ : Fin (r + 1))] = 0 := by
    have h_LP_entry :
        (Matrix.noPivotLoop s initLP).matrix[(⟨s, hs_lt_r1⟩ : Fin (r + 1))][
          (⟨s, hs_lt_r1⟩ : Fin (r + 1))] =
        (Matrix.leadingPrefix (Matrix.noPivotLoop s initGM).matrix (r + 1) hK)[
          (⟨s, hs_lt_r1⟩ : Fin (r + 1))][
          (⟨s, hs_lt_r1⟩ : Fin (r + 1))] := by
      rw [← h_mat_sync]
    rw [h_LP_entry]
    rw [Matrix.leadingPrefix_entry (Matrix.noPivotLoop s initGM).matrix (r + 1) hK
      (⟨s, hs_lt_r1⟩ : Fin (r + 1)) (⟨s, hs_lt_r1⟩ : Fin (r + 1))]
    have h_idx_eq :
        (⟨s, Nat.lt_of_lt_of_le hs_lt_r1 hK⟩ : Fin n) =
          (⟨s, hsn⟩ : Fin n) := Fin.ext rfl
    have h_entry_eq :
        (Matrix.noPivotLoop s initGM).matrix[
          (⟨s, Nat.lt_of_lt_of_le hs_lt_r1 hK⟩ : Fin n)][
          (⟨s, Nat.lt_of_lt_of_le hs_lt_r1 hK⟩ : Fin n)] =
        (Matrix.noPivotLoop s initGM).matrix[(⟨s, hsn⟩ : Fin n)][(⟨s, hsn⟩ : Fin n)] :=
      matrix_diag_at_fin_eq _ h_idx_eq
    exact h_entry_eq.trans h_full_zero
  have h_LP_find_none :
      Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
        (⟨s, hs_lt_r1⟩ : Fin (r + 1)) (s + 1) = none :=
    Matrix.findPivot?_eq_none_of_zero _ _ _ h_LP_col_zero
  -- Step 7: pivotLoop on LP records singular at s.
  have h_LP_step_lt : (Matrix.noPivotLoop s initLP).step + 1 < r + 1 := by
    rw [h_LP_step]; omega
  have h_idx_at_LP_step :
      (⟨(Matrix.noPivotLoop s initLP).step,
        Nat.lt_of_succ_lt h_LP_step_lt⟩ : Fin (r + 1)) =
        (⟨s, hs_lt_r1⟩ : Fin (r + 1)) :=
    Fin.ext h_LP_step
  have h_LP_zero_at_result :
      (Matrix.noPivotLoop s initLP).matrix[
        (⟨(Matrix.noPivotLoop s initLP).step,
          Nat.lt_of_succ_lt h_LP_step_lt⟩ : Fin (r + 1))][
        (⟨(Matrix.noPivotLoop s initLP).step,
          Nat.lt_of_succ_lt h_LP_step_lt⟩ : Fin (r + 1))] = 0 :=
    (matrix_diag_at_fin_eq (n := r + 1)
      (Matrix.noPivotLoop s initLP).matrix h_idx_at_LP_step).trans h_LP_zero_diag
  have h_LP_find_at_result :
      Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
        (⟨(Matrix.noPivotLoop s initLP).step,
          Nat.lt_of_succ_lt h_LP_step_lt⟩ : Fin (r + 1))
        ((Matrix.noPivotLoop s initLP).step + 1) = none := by
    have h_step_plus_eq : (Matrix.noPivotLoop s initLP).step + 1 = s + 1 := by
      rw [h_LP_step]
    have h_step1 :
        Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
            (⟨(Matrix.noPivotLoop s initLP).step,
              Nat.lt_of_succ_lt h_LP_step_lt⟩ : Fin (r + 1))
            ((Matrix.noPivotLoop s initLP).step + 1) =
          Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
            (⟨s, hs_lt_r1⟩ : Fin (r + 1))
            ((Matrix.noPivotLoop s initLP).step + 1) :=
      congrArg
        (fun (i : Fin (r + 1)) =>
          Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix i
            ((Matrix.noPivotLoop s initLP).step + 1))
        h_idx_at_LP_step
    have h_step2 :
        Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
            (⟨s, hs_lt_r1⟩ : Fin (r + 1))
            ((Matrix.noPivotLoop s initLP).step + 1) =
          Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
            (⟨s, hs_lt_r1⟩ : Fin (r + 1))
            (s + 1) :=
      congrArg
        (fun (st : Nat) =>
          Matrix.findPivot? (Matrix.noPivotLoop s initLP).matrix
            (⟨s, hs_lt_r1⟩ : Fin (r + 1)) st)
        h_step_plus_eq
    exact (h_step1.trans h_step2).trans h_LP_find_none
  have h_pivot_sing : (Matrix.pivotLoop (r + 1) initLP).singularStep =
      some (Matrix.noPivotLoop s initLP).step :=
    pivotLoop_singularStep_some_of_partial_no_replacement
      s (r + 1) initLP (Matrix.noPivotLoop s initLP)
      rfl rfl (by omega) h_LP_sing h_LP_step_lt
      h_LP_zero_at_result h_LP_find_at_result
  -- Step 8: bareiss LP = 0 via singular branch of BareissData.det.
  have h_bareissData_sing :
      (Matrix.bareissData LP).singularStep =
        some (Matrix.noPivotLoop s initLP).step := by
    rw [Matrix.bareissData_eq_finish_pivotLoop]
    show (Matrix.pivotLoop (r + 1) initLP).singularStep =
      some (Matrix.noPivotLoop s initLP).step
    exact h_pivot_sing
  have h_bareiss_zero : Matrix.bareiss LP = 0 := by
    rw [Matrix.bareiss_eq_bareissData_det]
    unfold Matrix.BareissData.det
    rw [h_bareissData_sing]
  show (Matrix.bareiss LP).toNat = 0
  rw [h_bareiss_zero]
  rfl

/-- If the array loop's `state.step` is past the matrix extent, one outer
iteration returns the input state unchanged. -/
private theorem scaledCoeffArrayLoop_done (fuel : Nat)
    (state : ScaledCoeffArrayState) (hDone : ¬ state.step < n) :
    scaledCoeffArrayLoop n (fuel + 1) state = state := by
  simp [scaledCoeffArrayLoop, hDone]

/-- The array loop is idempotent once `state.step ≥ n`. -/
private theorem scaledCoeffArrayLoop_id_at_done (fuel : Nat)
    (state : ScaledCoeffArrayState) (hDone : ¬ state.step < n) :
    scaledCoeffArrayLoop n fuel state = state := by
  cases fuel with
  | zero => rfl
  | succ f => exact scaledCoeffArrayLoop_done f state hDone

/-- Singular branch of one array-loop iteration: a zero pivot strictly before
the last column halts the loop, writing the scaled column at the current step
but leaving the matrix and step untouched. -/
private theorem scaledCoeffArrayLoop_singular_branch (fuel : Nat)
    (state : ScaledCoeffArrayState)
    (hStep : state.step < n) (hNext : state.step + 1 < n)
    (hp : getArrayEntry state.matrix state.step state.step = 0) :
    scaledCoeffArrayLoop n (fuel + 1) state =
      { state with coeffs := writeScaledColumn state.coeffs state.matrix n state.step } := by
  simp [scaledCoeffArrayLoop, hStep, hNext, hp]

/-- Last-column branch of one array-loop iteration: when `state.step = n - 1`,
the loop writes the final scaled column and advances `step` to `n` without
applying a Bareiss step. -/
private theorem scaledCoeffArrayLoop_last_step (fuel : Nat)
    (state : ScaledCoeffArrayState)
    (hStep : state.step < n) (hNext : ¬ state.step + 1 < n) :
    scaledCoeffArrayLoop n (fuel + 1) state =
      { state with
        step := state.step + 1
        coeffs := writeScaledColumn state.coeffs state.matrix n state.step } := by
  simp [scaledCoeffArrayLoop, hStep, hNext]

/-- Regular branch of one array-loop iteration: a nonzero pivot strictly before
the last column applies one row-mutating Bareiss update, advances
`step`, records the new `prevPivot`, and recurses on the remaining fuel. -/
private theorem scaledCoeffArrayLoop_regular_branch (fuel : Nat)
    (state : ScaledCoeffArrayState)
    (hStep : state.step < n) (hNext : state.step + 1 < n)
    (hp : getArrayEntry state.matrix state.step state.step ≠ 0) :
    scaledCoeffArrayLoop n (fuel + 1) state =
      scaledCoeffArrayLoop n fuel
        { step := state.step + 1
          matrix := stepScaledRows state.matrix n state.step
            (getArrayEntry state.matrix state.step state.step) state.prevPivot
          coeffs := writeScaledColumn state.coeffs state.matrix n state.step
          prevPivot := getArrayEntry state.matrix state.step state.step } := by
  simp [scaledCoeffArrayLoop, hStep, hNext, hp]

/-- The matrix-side view of a row-storage entry: `getArrayEntry` on the array
matches the matrix-level `[i][j]` lookup under `rowsToMatrix`. -/
private theorem getArrayEntry_eq_rowsToMatrix
    (rows : Array (Array Int)) (i j : Fin n) :
    getArrayEntry rows i.val j.val = (rowsToMatrix rows n)[i][j] := by
  simp [rowsToMatrix, Matrix.ofFn]

/-- If the array loop is currently at column `j`, the coefficient entry below
the diagonal in that column records the pre-elimination matrix entry for that
same step. In the regular branch, later recursive iterations preserve column
`j` because the next state has advanced past it. -/
private theorem getArrayEntry_scaledCoeffArrayLoop_current_col_written
    (n fuel : Nat) (state : ScaledCoeffArrayState) (i j : Nat)
    (hstep : state.step = j) (hji : j < i) (hin : i < n)
    (h_coeffs_size : state.coeffs.size = n)
    (h_coeffs_rows_size : ∀ r, r < n → state.coeffs[r]!.size = n) :
    getArrayEntry (scaledCoeffArrayLoop n (fuel + 1) state).coeffs i j =
      getArrayEntry state.matrix i j := by
  have hArrayStep : state.step < n := by omega
  have hrow : i < state.coeffs.size := by
    rw [h_coeffs_size]
    exact hin
  have hcol : j < state.coeffs[i]!.size := by
    rw [h_coeffs_rows_size i hin]
    exact Nat.lt_trans hji hin
  by_cases hNext : state.step + 1 < n
  · by_cases hp : getArrayEntry state.matrix state.step state.step = 0
    · rw [scaledCoeffArrayLoop_singular_branch fuel state hArrayStep hNext hp]
      rw [hstep]
      exact getArrayEntry_writeScaledColumn_below state.coeffs state.matrix n j i
        hji hin hrow hcol
    · rw [scaledCoeffArrayLoop_regular_branch fuel state hArrayStep hNext hp]
      let next : ScaledCoeffArrayState :=
        { step := state.step + 1
          matrix := stepScaledRows state.matrix n state.step
            (getArrayEntry state.matrix state.step state.step) state.prevPivot
          coeffs := writeScaledColumn state.coeffs state.matrix n state.step
          prevPivot := getArrayEntry state.matrix state.step state.step }
      change getArrayEntry (scaledCoeffArrayLoop n fuel next).coeffs i j =
        getArrayEntry state.matrix i j
      rw [getArrayEntry_scaledCoeffArrayLoop_preserve_col_before_step]
      · show getArrayEntry (writeScaledColumn state.coeffs state.matrix n state.step) i j =
          getArrayEntry state.matrix i j
        rw [hstep]
        exact getArrayEntry_writeScaledColumn_below state.coeffs state.matrix n j i
          hji hin hrow hcol
      · show j < next.step
        simp [next, hstep]
  · rw [scaledCoeffArrayLoop_last_step fuel state hArrayStep hNext]
    rw [hstep]
    exact getArrayEntry_writeScaledColumn_below state.coeffs state.matrix n j i
      hji hin hrow hcol

/-- Non-singular target-column lower-triangle capture. If the matrix-side
`noPivotLoop` reaches the target column `j` without recording a singular step,
then the scaled-coefficient array loop records at `(i,j)` the matrix entry from
the pre-elimination state at that target column. -/
private theorem scaledCoeffArrayLoop_lower_matches_target_column
    {state_array : ScaledCoeffArrayState} {state_matrix : Matrix.BareissState n}
    (h_step_eq : state_array.step = state_matrix.step)
    (h_matrix_eq : rowsToMatrix state_array.matrix n = state_matrix.matrix)
    (h_prev_eq : state_array.prevPivot = state_matrix.prevPivot)
    (h_array_size : state_array.matrix.size = n)
    (h_array_rows_size : ∀ r, r < n → state_array.matrix[r]!.size = n)
    (h_coeffs_size : state_array.coeffs.size = n)
    (h_coeffs_rows_size : ∀ r, r < n → state_array.coeffs[r]!.size = n)
    (fuel : Nat) (i j : Fin n)
    (h_step_le_j : state_matrix.step ≤ j.val)
    (hji : j.val < i.val)
    (h_fuel : j.val < state_matrix.step + fuel)
    (h_target_nonsing :
      (Matrix.noPivotLoop (j.val - state_matrix.step) state_matrix).singularStep = none) :
    getArrayEntry (scaledCoeffArrayLoop n fuel state_array).coeffs i.val j.val =
      (Matrix.noPivotLoop (j.val - state_matrix.step) state_matrix).matrix[i][j] := by
  induction fuel generalizing state_array state_matrix with
  | zero =>
      omega
  | succ fuel' ih =>
      by_cases h_at_target : state_matrix.step = j.val
      · have h_array_step : state_array.step = j.val := by
          rw [h_step_eq, h_at_target]
        rw [getArrayEntry_scaledCoeffArrayLoop_current_col_written n fuel' state_array
          i.val j.val h_array_step hji i.isLt h_coeffs_size h_coeffs_rows_size]
        have hdist : j.val - state_matrix.step = 0 := by omega
        rw [hdist, Matrix.noPivotLoop_zero_fuel]
        rw [getArrayEntry_eq_rowsToMatrix state_array.matrix i j]
        rw [h_matrix_eq]
      · have h_step_lt_j : state_matrix.step < j.val :=
          Nat.lt_of_le_of_ne h_step_le_j h_at_target
        have hDone : state_matrix.step + 1 < n := by
          omega
        have h_step_lt_n : state_matrix.step < n := Nat.lt_of_succ_lt hDone
        have hArrayStep : state_array.step < n := h_step_eq ▸ h_step_lt_n
        have hArrayNext : state_array.step + 1 < n := h_step_eq ▸ hDone
        let kFin : Fin n := ⟨state_matrix.step, h_step_lt_n⟩
        have h_pivot_array_eq_matrix :
            getArrayEntry state_array.matrix state_array.step state_array.step =
              state_matrix.matrix[kFin][kFin] := by
          rw [h_step_eq]
          have := getArrayEntry_eq_rowsToMatrix (n := n) state_array.matrix kFin kFin
          rw [this, h_matrix_eq]
        by_cases hp : state_matrix.matrix[kFin][kFin] = 0
        · have hdist :
              j.val - state_matrix.step = (j.val - (state_matrix.step + 1)) + 1 := by
            omega
          rw [hdist, Matrix.noPivotLoop_singular_branch _ state_matrix hDone hp] at h_target_nonsing
          simp at h_target_nonsing
        · have hp_array :
              getArrayEntry state_array.matrix state_array.step state_array.step ≠ 0 := by
            rw [h_pivot_array_eq_matrix]
            exact hp
          rw [scaledCoeffArrayLoop_regular_branch fuel' state_array hArrayStep hArrayNext hp_array]
          let new_array : ScaledCoeffArrayState :=
            { step := state_array.step + 1
              matrix := stepScaledRows state_array.matrix n state_array.step
                (getArrayEntry state_array.matrix state_array.step state_array.step)
                state_array.prevPivot
              coeffs := writeScaledColumn state_array.coeffs state_array.matrix n state_array.step
              prevPivot := getArrayEntry state_array.matrix state_array.step state_array.step }
          let new_matrix : Matrix.BareissState n :=
            { step := state_matrix.step + 1
              matrix := Matrix.stepMatrix state_matrix.matrix state_matrix.step
                state_matrix.matrix[kFin][kFin]
                state_matrix.prevPivot
              prevPivot := state_matrix.matrix[kFin][kFin]
              rowSwaps := state_matrix.rowSwaps
              singularStep := none }
          change getArrayEntry (scaledCoeffArrayLoop n fuel' new_array).coeffs i.val j.val =
            (Matrix.noPivotLoop (j.val - state_matrix.step) state_matrix).matrix[i][j]
          have h_step_new : new_array.step = new_matrix.step := by
            show state_array.step + 1 = state_matrix.step + 1
            rw [h_step_eq]
          have h_matrix_new : rowsToMatrix new_array.matrix n = new_matrix.matrix := by
            show rowsToMatrix
                (stepScaledRows state_array.matrix n state_array.step _ state_array.prevPivot) n =
              Matrix.stepMatrix state_matrix.matrix state_matrix.step _ state_matrix.prevPivot
            rw [rowsToMatrix_stepScaledRows_eq_stepMatrix _ _ _ _ h_array_size
              h_array_rows_size, h_matrix_eq, h_pivot_array_eq_matrix, h_step_eq, h_prev_eq]
          have h_prev_new : new_array.prevPivot = new_matrix.prevPivot := h_pivot_array_eq_matrix
          have h_array_size_new : new_array.matrix.size = n := by
            show (stepScaledRows state_array.matrix n state_array.step _ _).size = n
            rw [stepScaledRows_size, h_array_size]
          have h_array_rows_size_new : ∀ r, r < n → new_array.matrix[r]!.size = n := by
            intro r hr
            show (stepScaledRows state_array.matrix n state_array.step _ _)[r]!.size = n
            exact stepScaledRows_rows_size state_array.matrix n state_array.step _ _
              h_array_size h_array_rows_size r hr
          have h_coeffs_size_new : new_array.coeffs.size = n := by
            show (writeScaledColumn _ _ _ _).size = n
            rw [writeScaledColumn_size]
            exact h_coeffs_size
          have h_coeffs_rows_size_new : ∀ r, r < n → new_array.coeffs[r]!.size = n := by
            intro r hr
            show (writeScaledColumn _ _ _ _)[r]!.size = n
            rw [writeScaledColumn_rows_size]
            exact h_coeffs_rows_size r hr
          have h_step_le_j_new : new_matrix.step ≤ j.val := by
            show state_matrix.step + 1 ≤ j.val
            omega
          have h_fuel_new : j.val < new_matrix.step + fuel' := by
            show j.val < state_matrix.step + 1 + fuel'
            omega
          have h_target_nonsing_new :
              (Matrix.noPivotLoop (j.val - new_matrix.step) new_matrix).singularStep = none := by
            have hdist :
                j.val - state_matrix.step = (j.val - (state_matrix.step + 1)) + 1 := by
              omega
            rw [hdist, Matrix.noPivotLoop_regular_branch _ state_matrix hDone hp] at h_target_nonsing
            simpa [new_matrix] using h_target_nonsing
          have h_capture := ih h_step_new h_matrix_new h_prev_new h_array_size_new
            h_array_rows_size_new h_coeffs_size_new h_coeffs_rows_size_new
            h_step_le_j_new h_fuel_new h_target_nonsing_new
          have hdist :
              j.val - state_matrix.step = (j.val - (state_matrix.step + 1)) + 1 := by
            omega
          rw [h_capture]
          rw [hdist, Matrix.noPivotLoop_regular_branch _ state_matrix hDone hp]
          rfl

/-- Early-singular lower-column preservation before the singular column:
when the aligned matrix-side state sees a zero pivot at the current step, the
array loop halts after writing only that current column, so lower entries in
strictly earlier columns retain their already-captured matrix values. -/
private theorem scaledCoeffArrayLoop_lower_singular_before_step
    {state_array : ScaledCoeffArrayState} {state_matrix : Matrix.BareissState n}
    (h_step_eq : state_array.step = state_matrix.step)
    (h_matrix_eq : rowsToMatrix state_array.matrix n = state_matrix.matrix)
    (h_coeffs_processed : ∀ r c : Fin n,
      c.val < state_matrix.step → c.val < r.val →
        getArrayEntry state_array.coeffs r.val c.val = state_matrix.matrix[r][c])
    (fuel : Nat) (i j : Fin n)
    (hjs : j.val < state_matrix.step) (hji : j.val < i.val)
    (hDone : state_matrix.step + 1 < n)
    (hp : state_matrix.matrix[
        (⟨state_matrix.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
        (⟨state_matrix.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0) :
    getArrayEntry (scaledCoeffArrayLoop n (fuel + 1) state_array).coeffs i.val j.val =
      state_matrix.matrix[i][j] := by
  have hArrayStep : state_array.step < n := h_step_eq ▸ Nat.lt_of_succ_lt hDone
  have hArrayNext : state_array.step + 1 < n := h_step_eq ▸ hDone
  let kFin : Fin n := ⟨state_matrix.step, Nat.lt_of_succ_lt hDone⟩
  have hp_array :
      getArrayEntry state_array.matrix state_array.step state_array.step = 0 := by
    rw [h_step_eq]
    have := getArrayEntry_eq_rowsToMatrix (n := n) state_array.matrix kFin kFin
    rw [this, h_matrix_eq]
    exact hp
  rw [scaledCoeffArrayLoop_singular_branch fuel state_array hArrayStep hArrayNext hp_array]
  rw [getArrayEntry_writeScaledColumn_of_col_ne]
  · exact h_coeffs_processed i j hjs hji
  · rw [h_step_eq]
    omega

/-- Early-singular current-column capture: the singular column itself follows
`writeScaledColumn` semantics, recording the pre-step matrix-column value
before the array loop halts. -/
private theorem scaledCoeffArrayLoop_lower_singular_current_step
    {state_array : ScaledCoeffArrayState} {state_matrix : Matrix.BareissState n}
    (h_step_eq : state_array.step = state_matrix.step)
    (h_matrix_eq : rowsToMatrix state_array.matrix n = state_matrix.matrix)
    (h_coeffs_size : state_array.coeffs.size = n)
    (h_coeffs_rows_size : ∀ r, r < n → state_array.coeffs[r]!.size = n)
    (fuel : Nat) (i : Fin n)
    (hji : state_matrix.step < i.val)
    (hDone : state_matrix.step + 1 < n)
    (hp : state_matrix.matrix[
        (⟨state_matrix.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
        (⟨state_matrix.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0) :
    getArrayEntry (scaledCoeffArrayLoop n (fuel + 1) state_array).coeffs
        i.val state_array.step =
      state_matrix.matrix[i][
        (⟨state_matrix.step, Nat.lt_trans hji i.isLt⟩ : Fin n)] := by
  have hArrayStep : state_array.step < n := h_step_eq ▸ Nat.lt_of_succ_lt hDone
  have hArrayNext : state_array.step + 1 < n := h_step_eq ▸ hDone
  let kFin : Fin n := ⟨state_matrix.step, Nat.lt_of_succ_lt hDone⟩
  have hp_array :
      getArrayEntry state_array.matrix state_array.step state_array.step = 0 := by
    rw [h_step_eq]
    have := getArrayEntry_eq_rowsToMatrix (n := n) state_array.matrix kFin kFin
    rw [this, h_matrix_eq]
    exact hp
  have hrow : i.val < state_array.coeffs.size := by
    rw [h_coeffs_size]
    exact i.isLt
  have hcol : state_array.step < state_array.coeffs[i.val]!.size := by
    rw [h_coeffs_rows_size i.val i.isLt]
    exact hArrayStep
  rw [scaledCoeffArrayLoop_singular_branch fuel state_array hArrayStep hArrayNext hp_array]
  rw [getArrayEntry_writeScaledColumn_below state_array.coeffs state_array.matrix n
    state_array.step i.val]
  · let col_array : Fin n := ⟨state_array.step, hArrayStep⟩
    let col_matrix : Fin n := ⟨state_matrix.step, Nat.lt_trans hji i.isLt⟩
    have hcol_eq : col_array = col_matrix := Fin.ext h_step_eq
    have hentry :
        getArrayEntry state_array.matrix i.val state_array.step =
          (rowsToMatrix state_array.matrix n)[i][col_array] := by
      simp [rowsToMatrix, Matrix.ofFn, col_array]
    rw [hentry, h_matrix_eq]
    exact congrArg (fun c => state_matrix.matrix[i][c]) hcol_eq
  · rw [h_step_eq]
    exact hji
  · exact i.isLt
  · exact hrow
  · exact hcol

/-- Early-singular zero tail after the singular column: if the lower entries
in columns strictly after the current step are still unwritten before the
singular branch, writing the current column preserves that zero tail. -/
private theorem scaledCoeffArrayLoop_lower_singular_after_step
    {state_array : ScaledCoeffArrayState} {state_matrix : Matrix.BareissState n}
    (h_step_eq : state_array.step = state_matrix.step)
    (h_matrix_eq : rowsToMatrix state_array.matrix n = state_matrix.matrix)
    (h_coeffs_unwritten : ∀ r c : Fin n,
      state_matrix.step < c.val → c.val < r.val →
        getArrayEntry state_array.coeffs r.val c.val = 0)
    (fuel : Nat) (i j : Fin n)
    (hsj : state_matrix.step < j.val) (hji : j.val < i.val)
    (hDone : state_matrix.step + 1 < n)
    (hp : state_matrix.matrix[
        (⟨state_matrix.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
        (⟨state_matrix.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0) :
    getArrayEntry (scaledCoeffArrayLoop n (fuel + 1) state_array).coeffs i.val j.val = 0 := by
  have hArrayStep : state_array.step < n := h_step_eq ▸ Nat.lt_of_succ_lt hDone
  have hArrayNext : state_array.step + 1 < n := h_step_eq ▸ hDone
  let kFin : Fin n := ⟨state_matrix.step, Nat.lt_of_succ_lt hDone⟩
  have hp_array :
      getArrayEntry state_array.matrix state_array.step state_array.step = 0 := by
    rw [h_step_eq]
    have := getArrayEntry_eq_rowsToMatrix (n := n) state_array.matrix kFin kFin
    rw [this, h_matrix_eq]
    exact hp
  rw [scaledCoeffArrayLoop_singular_branch fuel state_array hArrayStep hArrayNext hp_array]
  rw [getArrayEntry_writeScaledColumn_of_col_ne]
  · exact h_coeffs_unwritten i j hsj hji
  · rw [h_step_eq]
    omega

/-- Packaged early-singular lower-column relation. At a zero pivot before the
last column, the array loop writes exactly the singular column and halts:
earlier lower columns keep their processed matrix values, the singular column
records the pre-step matrix entry, and later lower columns keep the unwritten
zero tail. -/
private theorem scaledCoeffArrayLoop_lower_singular_matches
    {state_array : ScaledCoeffArrayState} {state_matrix : Matrix.BareissState n}
    (h_step_eq : state_array.step = state_matrix.step)
    (h_matrix_eq : rowsToMatrix state_array.matrix n = state_matrix.matrix)
    (h_coeffs_size : state_array.coeffs.size = n)
    (h_coeffs_rows_size : ∀ r, r < n → state_array.coeffs[r]!.size = n)
    (h_coeffs_processed : ∀ r c : Fin n,
      c.val < state_matrix.step → c.val < r.val →
        getArrayEntry state_array.coeffs r.val c.val = state_matrix.matrix[r][c])
    (h_coeffs_unwritten : ∀ r c : Fin n,
      state_matrix.step < c.val → c.val < r.val →
        getArrayEntry state_array.coeffs r.val c.val = 0)
    (fuel : Nat) (i j : Fin n)
    (hji : j.val < i.val)
    (hDone : state_matrix.step + 1 < n)
    (hp : state_matrix.matrix[
        (⟨state_matrix.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
        (⟨state_matrix.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0) :
    (j.val < state_matrix.step ∧
      getArrayEntry (scaledCoeffArrayLoop n (fuel + 1) state_array).coeffs i.val j.val =
        state_matrix.matrix[i][j]) ∨
    (j.val = state_matrix.step ∧
      getArrayEntry (scaledCoeffArrayLoop n (fuel + 1) state_array).coeffs
          i.val state_array.step =
        state_matrix.matrix[i][j]) ∨
    (state_matrix.step < j.val ∧
      getArrayEntry (scaledCoeffArrayLoop n (fuel + 1) state_array).coeffs i.val j.val = 0) := by
  by_cases h_before : j.val < state_matrix.step
  · left
    refine ⟨h_before, ?_⟩
    exact scaledCoeffArrayLoop_lower_singular_before_step
      (n := n) (state_array := state_array) (state_matrix := state_matrix)
      h_step_eq h_matrix_eq h_coeffs_processed fuel i j h_before hji hDone hp
  · by_cases h_current : j.val = state_matrix.step
    · right
      left
      refine ⟨h_current, ?_⟩
      have hstep_lt_i : state_matrix.step < i.val := by omega
      have h_current_capture :=
        scaledCoeffArrayLoop_lower_singular_current_step
          (n := n) (state_array := state_array) (state_matrix := state_matrix)
          h_step_eq h_matrix_eq h_coeffs_size h_coeffs_rows_size fuel i
          hstep_lt_i hDone hp
      let stepFin : Fin n := ⟨state_matrix.step, Nat.lt_trans hstep_lt_i i.isLt⟩
      have hcol_eq : stepFin = j := Fin.ext h_current.symm
      exact h_current_capture.trans (congrArg (fun c => state_matrix.matrix[i][c]) hcol_eq)
    · right
      right
      have h_after : state_matrix.step < j.val := by omega
      refine ⟨h_after, ?_⟩
      exact scaledCoeffArrayLoop_lower_singular_after_step
        (n := n) (state_array := state_array) (state_matrix := state_matrix)
        h_step_eq h_matrix_eq h_coeffs_unwritten fuel i j h_after hji hDone hp

/-- State-level lower-triangle branch splitter for the scaled-coefficient
array loop. At a real matrix step, a zero pivot is discharged by the packaged
singular-column relation; a nonzero path to the target column is discharged by
the non-singular target-column capture theorem. -/
private theorem scaledCoeffArrayLoop_lower_matches
    {state_array : ScaledCoeffArrayState} {state_matrix : Matrix.BareissState n}
    (h_step_eq : state_array.step = state_matrix.step)
    (h_matrix_eq : rowsToMatrix state_array.matrix n = state_matrix.matrix)
    (h_prev_eq : state_array.prevPivot = state_matrix.prevPivot)
    (h_array_size : state_array.matrix.size = n)
    (h_array_rows_size : ∀ r, r < n → state_array.matrix[r]!.size = n)
    (h_coeffs_size : state_array.coeffs.size = n)
    (h_coeffs_rows_size : ∀ r, r < n → state_array.coeffs[r]!.size = n)
    (h_coeffs_processed : ∀ r c : Fin n,
      c.val < state_matrix.step → c.val < r.val →
        getArrayEntry state_array.coeffs r.val c.val = state_matrix.matrix[r][c])
    (h_coeffs_unwritten : ∀ r c : Fin n,
      state_matrix.step < c.val → c.val < r.val →
        getArrayEntry state_array.coeffs r.val c.val = 0)
    (fuel : Nat) (i j : Fin n)
    (h_step_le_j : state_matrix.step ≤ j.val)
    (hji : j.val < i.val)
    (h_fuel : j.val < state_matrix.step + (fuel + 1))
    (hDone : state_matrix.step + 1 < n) :
    ((hp : state_matrix.matrix[
        (⟨state_matrix.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
        (⟨state_matrix.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] = 0) →
      (j.val < state_matrix.step ∧
        getArrayEntry (scaledCoeffArrayLoop n (fuel + 1) state_array).coeffs i.val j.val =
          state_matrix.matrix[i][j]) ∨
      (j.val = state_matrix.step ∧
        getArrayEntry (scaledCoeffArrayLoop n (fuel + 1) state_array).coeffs
            i.val state_array.step =
          state_matrix.matrix[i][j]) ∨
      (state_matrix.step < j.val ∧
        getArrayEntry (scaledCoeffArrayLoop n (fuel + 1) state_array).coeffs i.val j.val = 0)) ∧
    ((hp : state_matrix.matrix[
        (⟨state_matrix.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)][
        (⟨state_matrix.step, Nat.lt_of_succ_lt hDone⟩ : Fin n)] ≠ 0) →
      (h_target_nonsing :
        (Matrix.noPivotLoop (j.val - state_matrix.step) state_matrix).singularStep = none) →
      getArrayEntry (scaledCoeffArrayLoop n (fuel + 1) state_array).coeffs i.val j.val =
        (Matrix.noPivotLoop (j.val - state_matrix.step) state_matrix).matrix[i][j]) := by
  constructor
  · intro hp
    exact scaledCoeffArrayLoop_lower_singular_matches
      (n := n) (state_array := state_array) (state_matrix := state_matrix)
      h_step_eq h_matrix_eq h_coeffs_size h_coeffs_rows_size
      h_coeffs_processed h_coeffs_unwritten fuel i j hji hDone hp
  · intro _hp h_target_nonsing
    exact scaledCoeffArrayLoop_lower_matches_target_column
      (n := n) (state_array := state_array) (state_matrix := state_matrix)
      h_step_eq h_matrix_eq h_prev_eq h_array_size h_array_rows_size
      h_coeffs_size h_coeffs_rows_size (fuel + 1) i j h_step_le_j hji
      h_fuel h_target_nonsing

/-- Singular dual of `scaledCoeffArrayLoop_lower_matches_target_column`.
When the matrix-side `noPivotLoop` records a singular step strictly before
reaching column `j`, the array loop halts at the singular column and the
target column is left at its initial (unwritten) zero value. -/
private theorem scaledCoeffArrayLoop_lower_zero_of_singular_before_target
    {state_array : ScaledCoeffArrayState} {state_matrix : Matrix.BareissState n}
    (h_step_eq : state_array.step = state_matrix.step)
    (h_matrix_eq : rowsToMatrix state_array.matrix n = state_matrix.matrix)
    (h_prev_eq : state_array.prevPivot = state_matrix.prevPivot)
    (h_array_size : state_array.matrix.size = n)
    (h_array_rows_size : ∀ r, r < n → state_array.matrix[r]!.size = n)
    (h_coeffs_size : state_array.coeffs.size = n)
    (h_coeffs_rows_size : ∀ r, r < n → state_array.coeffs[r]!.size = n)
    (h_coeffs_unwritten : ∀ r c : Fin n,
      state_matrix.step < c.val → c.val < r.val →
        getArrayEntry state_array.coeffs r.val c.val = 0)
    (h_no_sing : state_matrix.singularStep = none)
    (fuel : Nat) (i j : Fin n)
    (h_step_le_j : state_matrix.step ≤ j.val)
    (hji : j.val < i.val)
    (h_fuel : j.val < state_matrix.step + fuel)
    (s : Nat)
    (h_sing : (Matrix.noPivotLoop (j.val - state_matrix.step) state_matrix).singularStep
        = some s) :
    getArrayEntry (scaledCoeffArrayLoop n fuel state_array).coeffs i.val j.val = 0 := by
  induction fuel generalizing state_array state_matrix with
  | zero => omega
  | succ fuel' ih =>
      by_cases h_at_target : state_matrix.step = j.val
      · have hdist : j.val - state_matrix.step = 0 := by omega
        rw [hdist, Matrix.noPivotLoop_zero_fuel] at h_sing
        rw [h_no_sing] at h_sing
        nomatch h_sing
      · have h_step_lt_j : state_matrix.step < j.val :=
          Nat.lt_of_le_of_ne h_step_le_j h_at_target
        have hDone : state_matrix.step + 1 < n := by
          have := i.isLt
          omega
        have h_step_lt_n : state_matrix.step < n := Nat.lt_of_succ_lt hDone
        have hArrayStep : state_array.step < n := h_step_eq ▸ h_step_lt_n
        have hArrayNext : state_array.step + 1 < n := h_step_eq ▸ hDone
        let kFin : Fin n := ⟨state_matrix.step, h_step_lt_n⟩
        have h_pivot_array_eq_matrix :
            getArrayEntry state_array.matrix state_array.step state_array.step =
              state_matrix.matrix[kFin][kFin] := by
          rw [h_step_eq]
          have := getArrayEntry_eq_rowsToMatrix (n := n) state_array.matrix kFin kFin
          rw [this, h_matrix_eq]
        by_cases hp : state_matrix.matrix[kFin][kFin] = 0
        · exact scaledCoeffArrayLoop_lower_singular_after_step
            (n := n) (state_array := state_array) (state_matrix := state_matrix)
            h_step_eq h_matrix_eq h_coeffs_unwritten fuel' i j h_step_lt_j hji hDone hp
        · have hp_array :
              getArrayEntry state_array.matrix state_array.step state_array.step ≠ 0 := by
            rw [h_pivot_array_eq_matrix]
            exact hp
          rw [scaledCoeffArrayLoop_regular_branch fuel' state_array hArrayStep
            hArrayNext hp_array]
          let new_array : ScaledCoeffArrayState :=
            { step := state_array.step + 1
              matrix := stepScaledRows state_array.matrix n state_array.step
                (getArrayEntry state_array.matrix state_array.step state_array.step)
                state_array.prevPivot
              coeffs := writeScaledColumn state_array.coeffs state_array.matrix n
                state_array.step
              prevPivot := getArrayEntry state_array.matrix state_array.step state_array.step }
          let new_matrix : Matrix.BareissState n :=
            { step := state_matrix.step + 1
              matrix := Matrix.stepMatrix state_matrix.matrix state_matrix.step
                state_matrix.matrix[kFin][kFin]
                state_matrix.prevPivot
              prevPivot := state_matrix.matrix[kFin][kFin]
              rowSwaps := state_matrix.rowSwaps
              singularStep := none }
          change getArrayEntry (scaledCoeffArrayLoop n fuel' new_array).coeffs i.val j.val = 0
          have h_step_new : new_array.step = new_matrix.step := by
            show state_array.step + 1 = state_matrix.step + 1
            rw [h_step_eq]
          have h_matrix_new : rowsToMatrix new_array.matrix n = new_matrix.matrix := by
            show rowsToMatrix
                (stepScaledRows state_array.matrix n state_array.step _
                  state_array.prevPivot) n =
              Matrix.stepMatrix state_matrix.matrix state_matrix.step _ state_matrix.prevPivot
            rw [rowsToMatrix_stepScaledRows_eq_stepMatrix _ _ _ _ h_array_size
              h_array_rows_size, h_matrix_eq, h_pivot_array_eq_matrix, h_step_eq, h_prev_eq]
          have h_prev_new : new_array.prevPivot = new_matrix.prevPivot :=
            h_pivot_array_eq_matrix
          have h_array_size_new : new_array.matrix.size = n := by
            show (stepScaledRows state_array.matrix n state_array.step _ _).size = n
            rw [stepScaledRows_size, h_array_size]
          have h_array_rows_size_new : ∀ r, r < n → new_array.matrix[r]!.size = n := by
            intro r hr
            show (stepScaledRows state_array.matrix n state_array.step _
              state_array.prevPivot)[r]!.size = n
            exact stepScaledRows_rows_size state_array.matrix n state_array.step _ _
              h_array_size h_array_rows_size r hr
          have h_coeffs_size_new : new_array.coeffs.size = n := by
            show (writeScaledColumn _ _ _ _).size = n
            rw [writeScaledColumn_size]
            exact h_coeffs_size
          have h_coeffs_rows_size_new : ∀ r, r < n → new_array.coeffs[r]!.size = n := by
            intro r hr
            show (writeScaledColumn _ _ _ _)[r]!.size = n
            rw [writeScaledColumn_rows_size]
            exact h_coeffs_rows_size r hr
          have h_coeffs_unwritten_new : ∀ r c : Fin n,
              new_matrix.step < c.val → c.val < r.val →
                getArrayEntry new_array.coeffs r.val c.val = 0 := by
            intro r c hsc hcr
            show getArrayEntry
                (writeScaledColumn state_array.coeffs state_array.matrix n
                  state_array.step) r.val c.val = 0
            have hsc' : state_matrix.step + 1 < c.val := hsc
            have hc_ne_step : c.val ≠ state_array.step := by
              rw [h_step_eq]; omega
            rw [getArrayEntry_writeScaledColumn_of_col_ne _ _ _ _ _ _ hc_ne_step]
            exact h_coeffs_unwritten r c (by omega) hcr
          have h_no_sing_new : new_matrix.singularStep = none := rfl
          have h_step_le_j_new : new_matrix.step ≤ j.val := by
            show state_matrix.step + 1 ≤ j.val
            omega
          have h_fuel_new : j.val < new_matrix.step + fuel' := by
            show j.val < state_matrix.step + 1 + fuel'
            omega
          have h_sing_new :
              (Matrix.noPivotLoop (j.val - new_matrix.step) new_matrix).singularStep
                = some s := by
            have hdist :
                j.val - state_matrix.step = (j.val - (state_matrix.step + 1)) + 1 := by
              omega
            rw [hdist, Matrix.noPivotLoop_regular_branch _ state_matrix hDone hp] at h_sing
            simpa [new_matrix] using h_sing
          exact ih h_step_new h_matrix_new h_prev_new h_array_size_new
            h_array_rows_size_new h_coeffs_size_new h_coeffs_rows_size_new
            h_coeffs_unwritten_new h_no_sing_new h_step_le_j_new h_fuel_new
            h_sing_new

/-- State-level diagonal correspondence between the scaled-coefficient array
loop and the matrix-level `Matrix.noPivotLoop` on the same Gram-like data.

After running both loops for `fuel` iterations from compatible starting states
(matching steps, matrices, and `prevPivot`, with no recorded singular step
upstream and the coeffs invariant for already-processed columns), the
diagonal coefficient at every position `i` either matches the matrix-level
diagonal of `noPivotLoop` (when no singular step has been hit at or before
`i`) or is recorded as zero (when singular at some `s ≤ i`). This captures
the loop-level interpretation of `gramDetVecEntry` against the executable
array trajectory. -/
private theorem scaledCoeffArrayLoop_diag_matches
    {state_array : ScaledCoeffArrayState} {state_matrix : Matrix.BareissState n}
    (h_step_eq : state_array.step = state_matrix.step)
    (h_matrix_eq : rowsToMatrix state_array.matrix n = state_matrix.matrix)
    (h_prev_eq : state_array.prevPivot = state_matrix.prevPivot)
    (h_no_sing : state_matrix.singularStep = none)
    (h_array_size : state_array.matrix.size = n)
    (h_array_rows_size : ∀ r, r < n → state_array.matrix[r]!.size = n)
    (h_coeffs_size : state_array.coeffs.size = n)
    (h_coeffs_rows_size : ∀ r, r < n → state_array.coeffs[r]!.size = n)
    (h_coeffs_processed : ∀ j (_hjs : j < state_matrix.step) (hjn : j < n),
      getArrayEntry state_array.coeffs j j =
        state_matrix.matrix[(⟨j, hjn⟩ : Fin n)][(⟨j, hjn⟩ : Fin n)])
    (h_coeffs_unwritten : ∀ j (_hjs : state_matrix.step ≤ j) (_hjn : j < n),
      getArrayEntry state_array.coeffs j j = 0)
    (fuel : Nat) (i : Fin n)
    (h_fuel : i.val < state_matrix.step + fuel ∨ i.val < state_matrix.step) :
    ((Matrix.noPivotLoop fuel state_matrix).singularStep = none ∧
      getArrayEntry (scaledCoeffArrayLoop n fuel state_array).coeffs i.val i.val =
        (Matrix.noPivotLoop fuel state_matrix).matrix[i][i]) ∨
    (∃ s : Nat,
      (Matrix.noPivotLoop fuel state_matrix).singularStep = some s ∧
      ((s ≤ i.val ∧
        getArrayEntry (scaledCoeffArrayLoop n fuel state_array).coeffs i.val i.val = 0) ∨
       (i.val < s ∧
        getArrayEntry (scaledCoeffArrayLoop n fuel state_array).coeffs i.val i.val =
          (Matrix.noPivotLoop fuel state_matrix).matrix[i][i]))) := by
  induction fuel generalizing state_array state_matrix with
  | zero =>
      left
      refine ⟨h_no_sing, ?_⟩
      have h_ilt : i.val < state_matrix.step := by
        rcases h_fuel with hor1 | hor2
        · simpa using hor1
        · exact hor2
      exact h_coeffs_processed i.val h_ilt i.isLt
  | succ fuel' ih =>
      by_cases hDone : state_matrix.step + 1 < n
      · -- Subcase A: state_matrix.step + 1 < n. One real iteration.
        have h_step_lt_n : state_matrix.step < n := Nat.lt_of_succ_lt hDone
        have hArrayStep : state_array.step < n := h_step_eq ▸ h_step_lt_n
        have hArrayNext : state_array.step + 1 < n := h_step_eq ▸ hDone
        -- Build the pivot Fin index once.
        let kFin : Fin n := ⟨state_matrix.step, h_step_lt_n⟩
        -- Identify pivot equality between array and matrix views.
        have h_pivot_array_eq_matrix :
            getArrayEntry state_array.matrix state_array.step state_array.step =
              state_matrix.matrix[kFin][kFin] := by
          rw [h_step_eq]
          have := getArrayEntry_eq_rowsToMatrix (n := n) state_array.matrix kFin kFin
          rw [this, h_matrix_eq]
        by_cases hp : state_matrix.matrix[kFin][kFin] = 0
        · -- A1: singular branch.
          have hp_array : getArrayEntry state_array.matrix state_array.step state_array.step = 0 := by
            rw [h_pivot_array_eq_matrix]; exact hp
          rw [scaledCoeffArrayLoop_singular_branch fuel' state_array hArrayStep hArrayNext hp_array]
          rw [Matrix.noPivotLoop_singular_branch fuel' state_matrix hDone hp]
          right
          refine ⟨state_matrix.step, rfl, ?_⟩
          by_cases h_ilt : i.val < state_matrix.step
          · right
            refine ⟨h_ilt, ?_⟩
            change getArrayEntry
              (writeScaledColumn state_array.coeffs state_array.matrix n state_array.step) i.val i.val =
              state_matrix.matrix[i][i]
            rw [getArrayEntry_writeScaledColumn_of_col_ne _ _ _ _ _ _
              (show i.val ≠ state_array.step by rw [h_step_eq]; omega)]
            exact h_coeffs_processed i.val h_ilt i.isLt
          · have h_ilt : state_matrix.step ≤ i.val := Nat.le_of_not_lt h_ilt
            by_cases h_ieq : i.val = state_matrix.step
            · left
              refine ⟨Nat.le_of_eq h_ieq.symm, ?_⟩
              change getArrayEntry
                (writeScaledColumn state_array.coeffs state_array.matrix n state_array.step) i.val i.val =
                0
              have h_array_step_eq_i : state_array.step = i.val := by
                rw [h_step_eq]; exact h_ieq.symm
              rw [h_array_step_eq_i]
              have hrow : i.val < state_array.coeffs.size := by
                rw [h_coeffs_size]; exact i.isLt
              have hcol : i.val < state_array.coeffs[i.val]!.size := by
                rw [h_coeffs_rows_size i.val i.isLt]; exact i.isLt
              rw [getArrayEntry_writeScaledColumn_diag _ _ _ _ hrow hcol]
              -- Goal: getArrayEntry state_array.matrix i.val i.val = 0
              rw [← h_array_step_eq_i]
              exact hp_array
            · have h_igt : state_matrix.step < i.val :=
                Nat.lt_of_le_of_ne h_ilt fun h => h_ieq h.symm
              left
              refine ⟨Nat.le_of_lt h_igt, ?_⟩
              change getArrayEntry
                (writeScaledColumn state_array.coeffs state_array.matrix n state_array.step) i.val i.val =
                0
              rw [getArrayEntry_writeScaledColumn_of_col_ne _ _ _ _ _ _
                (show i.val ≠ state_array.step by rw [h_step_eq]; omega)]
              exact h_coeffs_unwritten i.val (Nat.le_of_lt h_igt) i.isLt
        · -- A2: regular branch.
          have hp_array : getArrayEntry state_array.matrix state_array.step state_array.step ≠ 0 := by
            rw [h_pivot_array_eq_matrix]; exact hp
          rw [scaledCoeffArrayLoop_regular_branch fuel' state_array hArrayStep hArrayNext hp_array]
          rw [Matrix.noPivotLoop_regular_branch fuel' state_matrix hDone hp]
          -- Build new compatible states.
          let new_array : ScaledCoeffArrayState :=
            { step := state_array.step + 1
              matrix := stepScaledRows state_array.matrix n state_array.step
                (getArrayEntry state_array.matrix state_array.step state_array.step)
                state_array.prevPivot
              coeffs := writeScaledColumn state_array.coeffs state_array.matrix n state_array.step
              prevPivot := getArrayEntry state_array.matrix state_array.step state_array.step }
          let new_matrix : Matrix.BareissState n :=
            { step := state_matrix.step + 1
              matrix := Matrix.stepMatrix state_matrix.matrix state_matrix.step
                state_matrix.matrix[kFin][kFin]
                state_matrix.prevPivot
              prevPivot := state_matrix.matrix[kFin][kFin]
              rowSwaps := state_matrix.rowSwaps
              singularStep := none }
          have h_step_new : new_array.step = new_matrix.step := by
            show state_array.step + 1 = state_matrix.step + 1
            rw [h_step_eq]
          have h_matrix_new : rowsToMatrix new_array.matrix n = new_matrix.matrix := by
            show rowsToMatrix
                (stepScaledRows state_array.matrix n state_array.step _ state_array.prevPivot) n =
              Matrix.stepMatrix state_matrix.matrix state_matrix.step _ state_matrix.prevPivot
            rw [rowsToMatrix_stepScaledRows_eq_stepMatrix _ _ _ _ h_array_size
              h_array_rows_size, h_matrix_eq, h_pivot_array_eq_matrix, h_step_eq, h_prev_eq]
          have h_prev_new : new_array.prevPivot = new_matrix.prevPivot := h_pivot_array_eq_matrix
          have h_no_sing_new : new_matrix.singularStep = none := rfl
          have h_array_size_new : new_array.matrix.size = n := by
            show (stepScaledRows state_array.matrix n state_array.step _ _).size = n
            rw [stepScaledRows_size, h_array_size]
          have h_array_rows_size_new : ∀ r, r < n → new_array.matrix[r]!.size = n := by
            intro r hr
            show (stepScaledRows state_array.matrix n state_array.step _ _)[r]!.size = n
            exact stepScaledRows_rows_size state_array.matrix n state_array.step _ _
              h_array_size h_array_rows_size r hr
          have h_coeffs_size_new : new_array.coeffs.size = n := by
            show (writeScaledColumn _ _ _ _).size = n
            rw [writeScaledColumn_size]; exact h_coeffs_size
          have h_coeffs_rows_size_new : ∀ r, r < n → new_array.coeffs[r]!.size = n := by
            intro r hr
            show (writeScaledColumn _ _ _ _)[r]!.size = n
            rw [writeScaledColumn_rows_size]; exact h_coeffs_rows_size r hr
          have h_coeffs_processed_new :
              ∀ j (_hjs : j < new_matrix.step) (hjn : j < n),
                getArrayEntry new_array.coeffs j j =
                  new_matrix.matrix[(⟨j, hjn⟩ : Fin n)][(⟨j, hjn⟩ : Fin n)] := by
            intro j hjs hjn
            let jFin : Fin n := ⟨j, hjn⟩
            change getArrayEntry (writeScaledColumn _ _ _ _) j j =
              (Matrix.stepMatrix state_matrix.matrix _ _ state_matrix.prevPivot)[jFin][jFin]
            have hj_le : jFin.val ≤ state_matrix.step := Nat.le_of_lt_succ hjs
            rw [Matrix.stepMatrix_diag_of_le _ _ _ _ _ hj_le]
            by_cases hj_eq : j = state_matrix.step
            · -- j = state_matrix.step = state_array.step
              have h_array_step_eq_j : state_array.step = j := h_step_eq.trans hj_eq.symm
              -- Rewrite writeScaledColumn's step argument to use j.
              have h_write_eq :
                  getArrayEntry
                      (writeScaledColumn state_array.coeffs state_array.matrix n state_array.step) j j =
                    getArrayEntry
                      (writeScaledColumn state_array.coeffs state_array.matrix n j) j j := by
                rw [h_array_step_eq_j]
              rw [h_write_eq]
              have hrow : j < state_array.coeffs.size := by
                rw [h_coeffs_size]; exact hjn
              have hcol : j < state_array.coeffs[j]!.size := by
                rw [h_coeffs_rows_size j hjn]; exact hjn
              rw [getArrayEntry_writeScaledColumn_diag _ _ _ _ hrow hcol]
              -- Goal: getArrayEntry state_array.matrix j j = state_matrix.matrix[jFin][jFin]
              rw [getArrayEntry_eq_rowsToMatrix state_array.matrix jFin jFin]
              rw [h_matrix_eq]
            · have hj_lt : j < state_matrix.step := Nat.lt_of_le_of_ne hj_le hj_eq
              rw [getArrayEntry_writeScaledColumn_of_col_ne _ _ _ _ _ _
                (show j ≠ state_array.step by rw [h_step_eq]; omega)]
              exact h_coeffs_processed j hj_lt hjn
          have h_coeffs_unwritten_new :
              ∀ j (_hjs : new_matrix.step ≤ j) (_hjn : j < n),
                getArrayEntry new_array.coeffs j j = 0 := by
            intro j hjs hjn
            show getArrayEntry (writeScaledColumn _ _ _ _) j j = 0
            have hj_gt : state_matrix.step < j := hjs
            rw [getArrayEntry_writeScaledColumn_of_col_ne _ _ _ _ _ _
              (show j ≠ state_array.step by rw [h_step_eq]; omega)]
            exact h_coeffs_unwritten j (Nat.le_of_lt hj_gt) hjn
          have h_fuel_new : i.val < new_matrix.step + fuel' ∨ i.val < new_matrix.step := by
            show i.val < state_matrix.step + 1 + fuel' ∨ i.val < state_matrix.step + 1
            rcases h_fuel with hor1 | hor2
            · left; omega
            · right; omega
          exact ih h_step_new h_matrix_new h_prev_new h_no_sing_new h_array_size_new
            h_array_rows_size_new h_coeffs_size_new h_coeffs_rows_size_new
            h_coeffs_processed_new h_coeffs_unwritten_new h_fuel_new
      · -- Subcase B: state_matrix.step + 1 ≥ n.
        rw [Matrix.noPivotLoop_done fuel' state_matrix hDone]
        left
        refine ⟨h_no_sing, ?_⟩
        by_cases hArrayStep : state_array.step < n
        · have hArrayNext : ¬ state_array.step + 1 < n := h_step_eq ▸ hDone
          rw [scaledCoeffArrayLoop_last_step fuel' state_array hArrayStep hArrayNext]
          by_cases h_ieq : i.val = state_matrix.step
          · have h_array_step_eq_i : state_array.step = i.val := by
              rw [h_step_eq]; exact h_ieq.symm
            change getArrayEntry (writeScaledColumn _ _ _ _) i.val i.val = _
            have h_rewrite_step :
                getArrayEntry
                    (writeScaledColumn state_array.coeffs state_array.matrix n state_array.step) i.val i.val =
                  getArrayEntry
                    (writeScaledColumn state_array.coeffs state_array.matrix n i.val) i.val i.val := by
              rw [h_array_step_eq_i]
            rw [h_rewrite_step]
            have hrow : i.val < state_array.coeffs.size := by
              rw [h_coeffs_size]; exact i.isLt
            have hcol : i.val < state_array.coeffs[i.val]!.size := by
              rw [h_coeffs_rows_size i.val i.isLt]; exact i.isLt
            rw [getArrayEntry_writeScaledColumn_diag _ _ _ _ hrow hcol]
            rw [getArrayEntry_eq_rowsToMatrix state_array.matrix i i]
            rw [h_matrix_eq]
          · by_cases h_ilt : i.val < state_matrix.step
            · change getArrayEntry (writeScaledColumn _ _ _ _) i.val i.val = _
              rw [getArrayEntry_writeScaledColumn_of_col_ne _ _ _ _ _ _
                (show i.val ≠ state_array.step by rw [h_step_eq]; omega)]
              exact h_coeffs_processed i.val h_ilt i.isLt
            · have h_ilt : state_matrix.step ≤ i.val := Nat.le_of_not_lt h_ilt
              have h_igt : state_matrix.step < i.val :=
                Nat.lt_of_le_of_ne h_ilt fun h => h_ieq h.symm
              have hDone : ¬ state_matrix.step + 1 < n := hDone
              omega
        · rw [scaledCoeffArrayLoop_id_at_done (fuel' + 1) state_array hArrayStep]
          have hArrayStep' : n ≤ state_array.step := Nat.le_of_not_lt hArrayStep
          have h_ilt : i.val < state_matrix.step := by
            rw [← h_step_eq]; exact Nat.lt_of_lt_of_le i.isLt hArrayStep'
          exact h_coeffs_processed i.val h_ilt i.isLt
/-- The no-pivot Bareiss pass over the full Gram matrix records the same
leading-prefix determinant as the public `gramDet` API at every vector slot.

This sorry is the consumer side of the singular helper
`leadingPrefix_gram_bareiss_toNat_eq_zero_of_noPivot_singular`. Discharging it
requires propagating quotient provenance through this private theorem
and its public consumers (`gramDetVecEntry_eq_gramDet`, `scaledCoeffs_diag_toNat`,
`gramDetVec_eq_gramDet`, and downstream callers in
`HexGramSchmidtMathlib` and `HexLLL`). That API surgery is tracked by #5655. -/
private theorem gramDetVecEntry_eq_leadingPrefix_bareiss
    (b : Matrix Int n m) (r : Nat) (hr : r < n) :
    gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
        ⟨r + 1, Nat.succ_lt_succ hr⟩ =
      (Matrix.bareiss
        (Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1)
          (Nat.succ_le_of_lt hr))).toNat := by
  sorry

/-- The no-pivot Bareiss pass over the full Gram matrix records the same
leading-prefix determinant as the public `gramDet` API at every vector slot. -/
theorem gramDetVecEntry_eq_gramDet
    (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) :
    gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
        ⟨k, Nat.lt_succ_of_le hk⟩ =
      gramDet b k hk := by
  cases k with
  | zero =>
      rw [show hk = Nat.zero_le n from Subsingleton.elim _ _]
      rfl
  | succ r =>
      have hr : r < n := Nat.lt_of_succ_le hk
      calc
        gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
            ⟨r + 1, Nat.lt_succ_of_le hk⟩ =
          gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
            ⟨r + 1, Nat.succ_lt_succ hr⟩ := by
              rfl
        _ = (Matrix.bareiss
              (Matrix.leadingPrefix (Matrix.gramMatrix b) (r + 1)
                (Nat.succ_le_of_lt hr))).toNat :=
              gramDetVecEntry_eq_leadingPrefix_bareiss (b := b) r hr
        _ = gramDet b (r + 1) hk := by
              simp [gramDet, GramSchmidt.leadingGramMatrixInt_eq_leadingPrefix_gram]


/-- The scaled-coefficient array loop writes the same diagonal determinant
values as `gramDetVecEntry`, including the zero tail after an early singular
no-pivot Bareiss step. -/
private theorem scaledCoeffRows_diag_toNat_eq_gramDetVecEntry
    (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    (getArrayEntry (scaledCoeffRows b) i i).toNat =
      gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
        ⟨i + 1, Nat.succ_lt_succ hi⟩ := by
  let iFin : Fin n := ⟨i, hi⟩
  have hdiag :=
    scaledCoeffArrayLoop_diag_matches
      (state_array :=
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 })
      (state_matrix := Matrix.noPivotInitialState (Matrix.gramMatrix b))
      (by rfl) (rowsToMatrix_gramRows b) (by rfl) (by rfl)
      (gramRows_size b) (gramRows_row_size b)
      (zeroRows_size n) (zeroRows_row_size n)
      (by
        intro j hjs _hjn
        simp [Matrix.noPivotInitialState] at hjs)
      (by
        intro j _hjs _hjn
        exact getArrayEntry_zeroRows n j j)
      n iFin (by
        left
        simp [Matrix.noPivotInitialState, iFin, hi])
  show (getArrayEntry
      (scaledCoeffArrayLoop n n
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 }).coeffs i i).toNat =
    gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
      ⟨i + 1, Nat.succ_lt_succ hi⟩
  rcases hdiag with ⟨h_sing, h_eq⟩ | ⟨s, h_sing, h_cases⟩
  · simp only [Matrix.bareissNoPivotData, gramDetVecEntry, Matrix.finish,
      bareissDiagNat, h_sing]
    exact congrArg Int.toNat h_eq
  · simp only [Matrix.bareissNoPivotData, gramDetVecEntry, Matrix.finish,
      bareissDiagNat, h_sing]
    rcases h_cases with ⟨hsi, h_zero⟩ | ⟨his, h_eq⟩
    · have hsi' : s ≤ i := by
        simpa [iFin] using hsi
      have hs_lt : s < i + 1 := by omega
      rw [if_pos hs_lt]
      exact congrArg Int.toNat h_zero
    · have his' : i < s := by
        simpa [iFin] using his
      have hs_not_lt : ¬ s < i + 1 := by omega
      rw [if_neg hs_not_lt]
      exact congrArg Int.toNat h_eq

/-- The scaled-coefficient loop stores the next leading Gram determinant on
the diagonal, at the executable Nat boundary. -/
private theorem scaledCoeffRows_diag_toNat_eq_gramDet
    (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    (getArrayEntry (scaledCoeffRows b) i i).toNat =
      gramDet b (i + 1) (Nat.succ_le_of_lt hi) := by
  rw [scaledCoeffRows_diag_toNat_eq_gramDetVecEntry (b := b) i hi]
  rw [gramDetVecEntry_eq_gramDet (b := b) (i + 1) (Nat.succ_le_of_lt hi)]

/-- Signed diagonal information from the executable scaled-coefficient loop:
the diagonal slot is either the zero tail recorded after an earlier singular
no-pivot step, or the signed diagonal entry in the final no-pivot Bareiss
matrix for the full Gram matrix. -/
private theorem scaledCoeffRows_diag_eq_zero_or_eq_noPivotData_diag
    (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    getArrayEntry (scaledCoeffRows b) i i = 0 ∨
      getArrayEntry (scaledCoeffRows b) i i =
        (Matrix.bareissNoPivotData (Matrix.gramMatrix b)).matrix[
          (⟨i, hi⟩ : Fin n)][(⟨i, hi⟩ : Fin n)] := by
  let iFin : Fin n := ⟨i, hi⟩
  have hdiag :=
    scaledCoeffArrayLoop_diag_matches
      (state_array :=
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 })
      (state_matrix := Matrix.noPivotInitialState (Matrix.gramMatrix b))
      (by rfl) (rowsToMatrix_gramRows b) (by rfl) (by rfl)
      (gramRows_size b) (gramRows_row_size b)
      (zeroRows_size n) (zeroRows_row_size n)
      (by
        intro j hjs _hjn
        simp [Matrix.noPivotInitialState] at hjs)
      (by
        intro j _hjs _hjn
        exact getArrayEntry_zeroRows n j j)
      n iFin (by
        left
        simp [Matrix.noPivotInitialState, iFin, hi])
  show getArrayEntry
      (scaledCoeffArrayLoop n n
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 }).coeffs i i = 0 ∨
    getArrayEntry
      (scaledCoeffArrayLoop n n
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 }).coeffs i i =
        (Matrix.bareissNoPivotData (Matrix.gramMatrix b)).matrix[iFin][iFin]
  rcases hdiag with ⟨_h_sing, h_eq⟩ | ⟨s, _h_sing, h_cases⟩
  · right
    simpa [Matrix.bareissNoPivotData, Matrix.finish, iFin] using h_eq
  · rcases h_cases with ⟨_hsi, h_zero⟩ | ⟨_his, h_eq⟩
    · left
      simpa [iFin] using h_zero
    · right
      simpa [Matrix.bareissNoPivotData, Matrix.finish, iFin] using h_eq

/-- Signed leading-prefix diagonal information from the executable
scaled-coefficient loop: the diagonal slot is either the zero tail after an
early singular no-pivot step, or the Bareiss determinant of the matching
leading Gram prefix. -/
private theorem scaledCoeffRows_diag_eq_zero_or_eq_leadingPrefix_bareiss
    (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    getArrayEntry (scaledCoeffRows b) i i = 0 ∨
      getArrayEntry (scaledCoeffRows b) i i =
        Matrix.bareiss
          (Matrix.leadingPrefix (Matrix.gramMatrix b) (i + 1)
            (Nat.succ_le_of_lt hi)) := by
  let iFin : Fin n := ⟨i, hi⟩
  have hdiag :=
    scaledCoeffArrayLoop_diag_matches
      (state_array :=
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 })
      (state_matrix := Matrix.noPivotInitialState (Matrix.gramMatrix b))
      (by rfl) (rowsToMatrix_gramRows b) (by rfl) (by rfl)
      (gramRows_size b) (gramRows_row_size b)
      (zeroRows_size n) (zeroRows_row_size n)
      (by
        intro j hjs _hjn
        simp [Matrix.noPivotInitialState] at hjs)
      (by
        intro j _hjs _hjn
        exact getArrayEntry_zeroRows n j j)
      n iFin (by
        left
        simp [Matrix.noPivotInitialState, iFin, hi])
  show getArrayEntry
      (scaledCoeffArrayLoop n n
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 }).coeffs i i = 0 ∨
    getArrayEntry
      (scaledCoeffArrayLoop n n
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 }).coeffs i i =
        Matrix.bareiss
          (Matrix.leadingPrefix (Matrix.gramMatrix b) (i + 1)
            (Nat.succ_le_of_lt hi))
  rcases hdiag with ⟨h_sing, h_eq⟩ | ⟨s, h_sing, h_cases⟩
  · right
    have h_final :
        (Matrix.noPivotLoop (i + (n - i))
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none := by
      have h_split : i + (n - i) = n := by omega
      simpa [h_split] using h_sing
    have h_prefix :
        (Matrix.noPivotLoop i
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none :=
      noPivotLoop_prefix_none_of_final_none i (n - i)
        (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl h_final
    have h_leading :=
      bareissNoPivotData_diag_eq_leadingPrefix_bareiss_of_prefix_nonsingular
        (b := b) i hi h_prefix
    have h_eq_noPivot :
        getArrayEntry
          (scaledCoeffArrayLoop n n
            { step := 0
              matrix := gramRows b
              coeffs := zeroRows n
              prevPivot := 1 }).coeffs i i =
          (Matrix.bareissNoPivotData (Matrix.gramMatrix b)).matrix[iFin][iFin] := by
      simpa [Matrix.bareissNoPivotData, Matrix.finish, iFin] using h_eq
    exact h_eq_noPivot.trans h_leading
  · rcases h_cases with ⟨_hsi, h_zero⟩ | ⟨his, h_eq⟩
    · left
      simpa [iFin] using h_zero
    · right
      have h_final :
          (Matrix.noPivotLoop (i + (n - i))
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s := by
        have h_split : i + (n - i) = n := by omega
        simpa [h_split] using h_sing
      have h_after : (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step + i ≤ s := by
        simp [Matrix.noPivotInitialState]
        have : i < s := by
          simpa [iFin] using his
        omega
      have h_prefix :
          (Matrix.noPivotLoop i
            (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none :=
        noPivotLoop_prefix_none_of_final_singular_after i (n - i)
          (Matrix.noPivotInitialState (Matrix.gramMatrix b)) rfl h_final h_after
      have h_leading :=
        bareissNoPivotData_diag_eq_leadingPrefix_bareiss_of_prefix_nonsingular
          (b := b) i hi h_prefix
      have h_eq_noPivot :
          getArrayEntry
            (scaledCoeffArrayLoop n n
              { step := 0
                matrix := gramRows b
                coeffs := zeroRows n
                prevPivot := 1 }).coeffs i i =
            (Matrix.bareissNoPivotData (Matrix.gramMatrix b)).matrix[iFin][iFin] := by
        simpa [Matrix.bareissNoPivotData, Matrix.finish, iFin] using h_eq
      exact h_eq_noPivot.trans h_leading

/-- If the diagonal executable entry is known nonnegative, the Nat-level
diagonal synchronization can be lifted back to the corresponding Int equality.
That nonnegativity is a Mathlib-side obligation for Gram determinants. -/
private theorem scaledCoeffRows_diag_eq_gramDet_of_nonneg
    (b : Matrix Int n m) (i : Nat) (hi : i < n)
    (hnonneg : 0 ≤ getArrayEntry (scaledCoeffRows b) i i) :
    getArrayEntry (scaledCoeffRows b) i i =
      Int.ofNat (gramDet b (i + 1) (Nat.succ_le_of_lt hi)) := by
  have hdiag := scaledCoeffRows_diag_toNat_eq_gramDet (b := b) i hi
  rw [← hdiag]
  exact (Int.toNat_of_nonneg hnonneg).symm

theorem gramDet_zero (b : Matrix Int n m) :
    gramDet b 0 (Nat.zero_le n) = 1 := by
  rfl

theorem gramDetVec_eq_gramDet (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) :
    (gramDetVec b).get ⟨k, Nat.lt_succ_of_le hk⟩ = gramDet b k hk := by
  sorry


/-- Nat-level diagonal synchronization for the public scaled-coefficient
matrix. This is the Mathlib-free diagonal fact exposed by the shared array
pass; the stronger Int-valued diagonal statement additionally needs a
nonnegativity proof for the Bareiss/Gram determinant slot. -/
theorem scaledCoeffs_diag_toNat (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    (GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨i, hi⟩).toNat =
      gramDet b (i + 1) (Nat.succ_le_of_lt hi) := by
  sorry

/-- Signed diagonal information for the public scaled-coefficient matrix.
The diagonal slot is either the zero tail recorded after an earlier singular
no-pivot step, or the signed diagonal entry in the final no-pivot Bareiss
matrix for the full Gram matrix. -/
theorem scaledCoeffs_diag_eq_zero_or_eq_noPivotData_diag
    (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨i, hi⟩ = 0 ∨
      GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨i, hi⟩ =
        (Matrix.bareissNoPivotData (Matrix.gramMatrix b)).matrix[
          (⟨i, hi⟩ : Fin n)][(⟨i, hi⟩ : Fin n)] := by
  sorry

/-- Signed diagonal information for the public scaled-coefficient matrix.
The diagonal slot is either the zero tail recorded after an earlier singular
no-pivot step, or the Bareiss determinant of the corresponding leading Gram
prefix. -/
theorem scaledCoeffs_diag_eq_zero_or_eq_leadingPrefix_bareiss
    (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨i, hi⟩ = 0 ∨
      GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨i, hi⟩ =
        Matrix.bareiss
          (Matrix.leadingPrefix (Matrix.gramMatrix b) (i + 1)
            (Nat.succ_le_of_lt hi)) := by
  sorry

theorem scaledCoeffs_diag_of_nonneg
    (b : Matrix Int n m) (i : Nat) (hi : i < n)
    (hnonneg : 0 ≤ GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨i, hi⟩) :
    GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨i, hi⟩ =
      Int.ofNat (gramDet b (i + 1) (Nat.succ_le_of_lt hi)) := by
  have hdiag := scaledCoeffs_diag_toNat (b := b) i hi
  rw [← hdiag]
  exact (Int.toNat_of_nonneg hnonneg).symm

theorem scaledCoeffs_upper (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i < j) :
    GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨j, hj⟩ = 0 := by
  sorry

private theorem foldl_add_eq_acc_rat_int {α : Type u}
    (xs : List α) (f : α → Rat) (acc : Rat)
    (hf : ∀ x ∈ xs, f x = 0) :
    xs.foldl (fun acc x => acc + f x) acc = acc := by
  induction xs generalizing acc with
  | nil =>
      simp only [List.foldl_nil]
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = 0 := hf x (by simp)
      have hxs : ∀ y ∈ xs, f y = 0 := fun y hy => hf y (List.mem_cons_of_mem _ hy)
      rw [hx]
      have hacc : acc + (0 : Rat) = acc := by grind
      rw [hacc]
      exact ih acc hxs

private theorem foldl_finRange_eq_prefix_of_zero_above_from
    {n : Nat} (k : Fin n) (f : Fin n → Rat) (acc : Rat)
    (hzero : ∀ j : Fin n, k.val < j.val → f j = 0) :
    (List.finRange n).foldl (fun acc j => acc + f j) acc =
      (List.finRange (k.val + 1)).foldl
        (fun acc j =>
          acc + f ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩) acc := by
  induction n generalizing acc with
  | zero =>
      exact Fin.elim0 k
  | succ n ih =>
      cases k using Fin.cases with
      | zero =>
          have htail : ∀ j ∈ (List.finRange n).map Fin.succ, f j = 0 := by
            intro j hj
            rcases List.mem_map.mp hj with ⟨i, _hi, rfl⟩
            exact hzero (Fin.succ i) (Nat.succ_pos i.val)
          have htailFold :
              ((List.finRange n).map Fin.succ).foldl (fun acc j => acc + f j)
                  (acc + f 0) = acc + f 0 :=
            foldl_add_eq_acc_rat_int ((List.finRange n).map Fin.succ) (fun j => f j)
              (acc + f 0) htail
          simpa [List.finRange_succ] using htailFold
      | succ k =>
          have hzero_tail : ∀ j : Fin n, k.val < j.val → f (Fin.succ j) = 0 := by
            intro j hj
            exact hzero (Fin.succ j) (Nat.succ_lt_succ hj)
          have htail := ih k (fun j => f (Fin.succ j)) (acc + f 0) hzero_tail
          have htail' :
              ((List.finRange n).map Fin.succ).foldl (fun acc j => acc + f j)
                  (acc + f 0) =
                ((List.finRange (k.val + 1)).map Fin.succ).foldl
                  (fun acc j =>
                    acc + f ⟨j.val,
                      Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt (Fin.succ k).isLt)⟩)
                  (acc + f 0) := by
            simpa [List.foldl_map] using htail
          simpa [List.finRange_succ, Nat.succ_eq_add_one, Nat.add_assoc] using htail'

private theorem foldl_finRange_eq_prefix_of_zero_above
    {n : Nat} (k : Fin n) (f : Fin n → Rat)
    (hzero : ∀ j : Fin n, k.val < j.val → f j = 0) :
    (List.finRange n).foldl (fun acc j => acc + f j) 0 =
      (List.finRange (k.val + 1)).foldl
        (fun acc j =>
          acc + f ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩) 0 :=
  foldl_finRange_eq_prefix_of_zero_above_from k f 0 hzero

/-- A `List.finRange (k + 1)` fold whose addend vanishes on every strict
predecessor of `k` reduces to the contribution at the last index. -/
private theorem foldl_finRange_succ_eq_last_of_zero_below
    (k : Nat) (f : Fin (k + 1) → Rat) (acc : Rat)
    (hzero : ∀ j : Fin (k + 1), j.val < k → f j = 0) :
    (List.finRange (k + 1)).foldl (fun acc j => acc + f j) acc =
      acc + f ⟨k, Nat.lt_succ_self k⟩ := by
  rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
  have hprefix :
      (List.finRange k).foldl
          (fun acc i => acc + f (Fin.castSucc i)) acc = acc := by
    refine foldl_add_eq_acc_rat_int (List.finRange k)
      (fun i => f (Fin.castSucc i)) acc ?_
    intro i _hi
    apply hzero
    change i.val < k
    exact i.isLt
  rw [hprefix]
  show acc + f (Fin.last k) = acc + f ⟨k, Nat.lt_succ_self k⟩
  rfl

/-- The `k`-th entry of the row combination of the Gram-Schmidt coefficient
matrix with a cast integer coefficient vector, when all later integer
coefficients vanish, equals the cast `k`-th coefficient.

This is the top Gram-Schmidt coordinate specialization consumed by the lattice
norm lower bound: rows below `k` contribute zero by upper-triangularity,
row `k` contributes one by the diagonal lemma, and rows above `k` contribute
zero because the corresponding integer coefficient vanishes. -/
theorem rowCombination_coeffs_apply_eq_of_zero_above
    (b : Matrix Int n m) (c : Vector Int n) (k : Fin n)
    (hzero_above : ∀ j : Fin n, k.val < j.val → c[j] = 0) :
    (Matrix.rowCombination (coeffs b)
        (Vector.map (fun x : Int => (x : Rat)) c))[k]
      = ((c[k] : Int) : Rat) := by
  let castc : Vector Rat n := Vector.map (fun x : Int => (x : Rat)) c
  have hcastc_get : ∀ i : Fin n, castc[i] = ((c[i] : Int) : Rat) := by
    intro i
    show (Vector.map (fun x : Int => (x : Rat)) c)[i.val]'i.isLt
        = ((c[i.val]'i.isLt : Int) : Rat)
    rw [Vector.getElem_map]
  -- Embed indices from the truncated prefix back into `Fin n`.
  let liftj : Fin (k.val + 1) → Fin n := fun j =>
    ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩
  rw [show
      (Matrix.rowCombination (coeffs b)
          (Vector.map (fun x : Int => (x : Rat)) c))[k]
        = (Matrix.rowCombination (coeffs b) castc)[k] from rfl]
  -- Step 1: rewrite the row-combination entry as a fold over the `k`-th column.
  have hcol :
      (Matrix.rowCombination (coeffs b) castc)[k]
        = (List.finRange n).foldl
            (fun acc i => acc + (coeffs b)[i][k] * castc[i]) 0 := by
    show ((coeffs b).transpose * castc)[k] = _
    rw [Matrix.mulVec_getElem]
    show Matrix.dot (((coeffs b).transpose).row k) castc = _
    show (List.finRange n).foldl
        (fun acc i =>
          acc + (((coeffs b).transpose).row k)[i] * castc[i]) 0 = _
    simp only [Matrix.row_getElem, Matrix.transpose_getElem]
  rw [hcol]
  -- Step 2: drop the tail above `k` via the zero-above truncation helper.
  let f : Fin n → Rat := fun i => (coeffs b)[i][k] * castc[i]
  have habove : ∀ j : Fin n, k.val < j.val → f j = 0 := by
    intro j hj
    show (coeffs b)[j][k] * castc[j] = 0
    rw [hcastc_get j]
    have hcj : c[j] = 0 := hzero_above j hj
    rw [hcj]
    show (coeffs b)[j][k] * (((0 : Int) : Rat)) = 0
    grind
  have htrunc :
      (List.finRange n).foldl (fun acc j => acc + f j) 0
        = (List.finRange (k.val + 1)).foldl
            (fun acc j => acc + f (liftj j)) 0 :=
    foldl_finRange_eq_prefix_of_zero_above k f habove
  show (List.finRange n).foldl (fun acc j => acc + f j) 0
      = ((c[k] : Int) : Rat)
  rw [htrunc]
  -- Step 3: isolate the contribution at `j = k`, using `coeffs_upper` for the
  -- entries strictly below `k`.
  let g : Fin (k.val + 1) → Rat := fun j => f (liftj j)
  have hbelow : ∀ j : Fin (k.val + 1), j.val < k.val → g j = 0 := by
    intro j hj
    show (coeffs b)[liftj j][k] * castc[liftj j] = 0
    have hentry :
        GramSchmidt.entry (coeffs b) (liftj j) k = 0 := by
      have h := coeffs_upper b j.val k.val
        (Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)) k.isLt hj
      have hkeq : (⟨k.val, k.isLt⟩ : Fin n) = k := Fin.ext rfl
      change GramSchmidt.entry (coeffs b) (liftj j) ⟨k.val, k.isLt⟩ = 0 at h
      rwa [hkeq] at h
    have : (coeffs b)[liftj j][k] = 0 := hentry
    rw [this]
    grind
  have hisolate :
      (List.finRange (k.val + 1)).foldl (fun acc j => acc + g j) 0
        = 0 + g ⟨k.val, Nat.lt_succ_self k.val⟩ :=
    foldl_finRange_succ_eq_last_of_zero_below k.val g 0 hbelow
  rw [hisolate]
  -- Step 4: evaluate `g` at the last index using `coeffs_diag`.
  change 0 + (coeffs b)[k][k] * castc[k] = ((c[k] : Int) : Rat)
  rw [hcastc_get k]
  have hdiag :
      GramSchmidt.entry (coeffs b) k k = 1 := by
    have h := coeffs_diag b k.val k.isLt
    have hkeq : (⟨k.val, k.isLt⟩ : Fin n) = k := Fin.ext rfl
    rwa [hkeq] at h
  have hkk : (coeffs b)[k][k] = 1 := hdiag
  rw [hkk]
  grind

/-! ### Prefix coefficient vector for integer row combinations -/

/-- Cast the first `k.val + 1` entries of an integer coefficient vector into a
rational prefix coefficient vector. Used to package an integer row combination
whose later coefficients vanish as a prefix-span witness over the cast input
rows. -/
private def prefixCoeffsCast (c : Vector Int n) (k : Fin n) : Vector Rat (k.val + 1) :=
  Vector.ofFn fun j : Fin (k.val + 1) =>
    let jn : Fin n := ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩
    (c[jn] : Rat)

/-- The last entry of `prefixCoeffsCast c k` is the rational cast of `c[k]`. -/
private theorem prefixCoeffsCast_last (c : Vector Int n) (k : Fin n) :
    (prefixCoeffsCast c k)[k.val]'(Nat.lt_succ_self k.val) = (c[k] : Rat) := by
  simp [prefixCoeffsCast]

/-- Integer cast distributes over an inner-product-style integer `foldl`. -/
private theorem foldl_int_dot_cast {n' : Nat}
    (xs : List (Fin n')) (g h : Fin n' → Int) (acc : Int) :
    ((xs.foldl (fun a i => a + g i * h i) acc : Int) : Rat) =
      xs.foldl
        (fun a i => a + ((g i : Rat)) * ((h i : Rat)))
        (acc : Rat) := by
  induction xs generalizing acc with
  | nil =>
      simp
  | cons i xs ih =>
      simp only [List.foldl_cons]
      have hpush : ((acc + g i * h i : Int) : Rat) =
          (acc : Rat) + (g i : Rat) * (h i : Rat) := by
        push_cast
        rfl
      have := ih (acc := acc + g i * h i)
      rw [this, hpush]

/-- Entry expansion of an integer row combination at a fixed output column. -/
private theorem rowCombination_int_getElem
    (b : Matrix Int n m) (c : Vector Int n) (col : Fin m) :
    (Matrix.rowCombination b c)[col] =
      (List.finRange n).foldl
        (fun (acc : Int) (i : Fin n) => acc + b[i][col] * c[i]) 0 := by
  show (Matrix.transpose b * c)[col] = _
  rw [Matrix.mulVec_getElem]
  show Matrix.dot ((Matrix.transpose b).row col) c = _
  simp [Matrix.dot, Hex.Vector.dotProduct, Matrix.row, Matrix.transpose, Matrix.col]

/-- The cast of an integer matrix to a rational matrix used by Gram-Schmidt.
This mirrors `GramSchmidt.castIntMatrix` (which is `private` in `Basic.lean`)
so we can refer to it directly inside `Int.lean`; the two definitions are
definitionally equal and unify against the term that appears in the statement
of `basis_span`. -/
private def castIntMatrix (b : Matrix Int n m) : Matrix Rat n m :=
  Vector.map (fun row => Vector.map (fun x : Int => (x : Rat)) row) b

/-- Entry expansion of the cast prefix row combination. The `(j + 1)`-row prefix
of `castIntMatrix b` combined with `prefixCoeffsCast c k` reads out as a sum of
the cast integer products through index `k`. -/
private theorem rowCombination_prefix_castIntMatrix_getElem
    (b : Matrix Int n m) (c : Vector Int n) (k : Fin n) (col : Fin m) :
    (Matrix.rowCombination
        (GramSchmidt.prefixRows (castIntMatrix b) k.val k.isLt)
        (prefixCoeffsCast c k))[col] =
      (List.finRange (k.val + 1)).foldl
        (fun (acc : Rat) (j : Fin (k.val + 1)) =>
          let jn : Fin n :=
            ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩
          acc + (b[jn][col] : Rat) * (c[jn] : Rat)) 0 := by
  show (Matrix.transpose _ * _)[col] = _
  rw [Matrix.mulVec_getElem]
  show Matrix.dot ((Matrix.transpose _).row col) _ = _
  simp [Matrix.dot, Hex.Vector.dotProduct, GramSchmidt.prefixRows,
    castIntMatrix, prefixCoeffsCast, Matrix.row, Matrix.transpose, Matrix.col]

/-- Cast row-combination prefix-span truncation. If an integer coefficient
vector has all entries above index `k` equal to zero, the cast of the integer
row combination is the row combination of the first `k.val + 1` cast rows with
the prefix coefficient vector `prefixCoeffsCast c k`. -/
private theorem cast_rowCombination_eq_prefix_rowCombination
    (b : Matrix Int n m) (c : Vector Int n) (k : Fin n)
    (hzero : ∀ j : Fin n, k.val < j.val → c[j] = 0) :
    Vector.map (fun x : Int => (x : Rat)) (Matrix.rowCombination b c) =
      Matrix.rowCombination
        (GramSchmidt.prefixRows (castIntMatrix b) k.val k.isLt)
        (prefixCoeffsCast c k) := by
  apply Vector.ext
  intro col hcol
  let cf : Fin m := ⟨col, hcol⟩
  have hLHS :
      (Vector.map (fun x : Int => (x : Rat)) (Matrix.rowCombination b c))[cf] =
        ((Matrix.rowCombination b c)[cf] : Rat) :=
    Vector.getElem_map _ _
  change (Vector.map (fun x : Int => (x : Rat)) (Matrix.rowCombination b c))[cf]
      = (Matrix.rowCombination
          (GramSchmidt.prefixRows (castIntMatrix b) k.val k.isLt)
          (prefixCoeffsCast c k))[cf]
  rw [hLHS]
  rw [rowCombination_int_getElem b c cf]
  rw [rowCombination_prefix_castIntMatrix_getElem b c k cf]
  -- LHS: cast of an integer foldl; RHS: a rational foldl over `finRange (k+1)`.
  -- First, push the cast through the integer foldl, getting a rational foldl
  -- over `finRange n` whose later terms vanish; then truncate to `k + 1`.
  rw [foldl_int_dot_cast (List.finRange n)
    (fun i : Fin n => b[i][cf]) (fun i : Fin n => c[i]) 0]
  let f : Fin n → Rat := fun i => (b[i][cf] : Rat) * (c[i] : Rat)
  have hfzero : ∀ j : Fin n, k.val < j.val → f j = 0 := by
    intro j hj
    have hcj : (c[j] : Rat) = 0 := by
      have : c[j] = 0 := hzero j hj
      simp [this]
    show (b[j][cf] : Rat) * (c[j] : Rat) = 0
    rw [hcj]
    grind
  have htrunc :=
    foldl_finRange_eq_prefix_of_zero_above (n := n) k f hfzero
  show (List.finRange n).foldl (fun acc i => acc + f i) ((0 : Int) : Rat) =
    (List.finRange (k.val + 1)).foldl
      (fun (acc : Rat) (j : Fin (k.val + 1)) =>
        let jn : Fin n :=
          ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt k.isLt)⟩
        acc + (b[jn][cf] : Rat) * (c[jn] : Rat)) 0
  have hcast0 : ((0 : Int) : Rat) = 0 := by norm_cast
  rw [hcast0]
  exact htrunc

/-- Cast row-combination prefix-span witness over the cast input rows. Under
the zero-tail hypothesis, the cast of an integer row combination lies in the
prefix span of the first `k.val + 1` cast input rows, with `prefixCoeffsCast c k`
as the explicit witness. -/
private theorem prefixSpan_castIntMatrix_of_rowCombination
    (b : Matrix Int n m) (c : Vector Int n) (k : Fin n)
    (hzero : ∀ j : Fin n, k.val < j.val → c[j] = 0) :
    GramSchmidt.prefixSpan (castIntMatrix b) k.val k.isLt
      (Vector.map (fun x : Int => (x : Rat)) (Matrix.rowCombination b c)) :=
  ⟨prefixCoeffsCast c k, (cast_rowCombination_eq_prefix_rowCombination b c k hzero).symm⟩

/-- Transport of `prefixSpan_castIntMatrix_of_rowCombination` through
`basis_span`: the cast integer row combination also lies in the prefix span of
the first `k.val + 1` Gram-Schmidt basis rows. -/
theorem prefixSpan_basis_of_rowCombination
    (b : Matrix Int n m) (c : Vector Int n) (k : Fin n)
    (hzero : ∀ j : Fin n, k.val < j.val → c[j] = 0) :
    GramSchmidt.prefixSpan (basis b) k.val k.isLt
      (Vector.map (fun x : Int => (x : Rat)) (Matrix.rowCombination b c)) :=
  (basis_span b k.val k.isLt _).mpr
    (prefixSpan_castIntMatrix_of_rowCombination b c k hzero)

/-- Package the prefix-span witness together with the recovered top
Gram-Schmidt coordinate for a lattice row combination whose integer
coefficients vanish above `k`. -/
theorem prefixSpan_basis_and_coeffs_apply_eq_of_rowCombination
    (b : Matrix Int n m) (c : Vector Int n) (k : Fin n)
    (hzero : ∀ j : Fin n, k.val < j.val → c[j] = 0) :
    GramSchmidt.prefixSpan (basis b) k.val k.isLt
        (Vector.map (fun x : Int => (x : Rat)) (Matrix.rowCombination b c)) ∧
      (Matrix.rowCombination (coeffs b)
          (Vector.map (fun x : Int => (x : Rat)) c))[k] = (c[k] : Rat) :=
  ⟨prefixSpan_basis_of_rowCombination b c k hzero,
    rowCombination_coeffs_apply_eq_of_zero_above b c k hzero⟩

/-- Nonzero specialization of
`prefixSpan_basis_and_coeffs_apply_eq_of_rowCombination`, for the highest
nonzero integer coefficient in a lattice row combination. -/
theorem prefixSpan_basis_and_coeffs_apply_ne_zero_of_rowCombination
    (b : Matrix Int n m) (c : Vector Int n) (k : Fin n)
    (hck : c[k] ≠ 0)
    (hzero : ∀ j : Fin n, k.val < j.val → c[j] = 0) :
    GramSchmidt.prefixSpan (basis b) k.val k.isLt
        (Vector.map (fun x : Int => (x : Rat)) (Matrix.rowCombination b c)) ∧
      (Matrix.rowCombination (coeffs b)
          (Vector.map (fun x : Int => (x : Rat)) c))[k] ≠ 0 := by
  refine ⟨prefixSpan_basis_of_rowCombination b c k hzero, ?_⟩
  rw [rowCombination_coeffs_apply_eq_of_zero_above b c k hzero]
  exact_mod_cast hck

/-- The coefficient matrix reconstructs the cast integer input rows from the
Gram-Schmidt basis rows. -/
theorem coeffs_mul_basis_eq_castIntMatrix (b : Matrix Int n m) :
    coeffs b * basis b = castIntMatrix b := by
  apply Vector.ext
  intro i hi
  let ii : Fin n := ⟨i, hi⟩
  apply Vector.ext
  intro j hj
  let jj : Fin m := ⟨j, hj⟩
  have hdec := basis_decomposition b i hi
  have hentry :
      ((basis b).row ii)[jj] +
        (GramSchmidt.prefixCombination (coeffs b) (basis b) i hi)[jj] =
      ((castIntMatrix b).row ii)[jj] := by
    have hdecj := congrArg (fun v : Vector Rat m => v[jj]) hdec
    simpa [castIntMatrix, Matrix.row, Vector.getElem_add] using hdecj.symm
  show (coeffs b * basis b)[ii][jj] = (castIntMatrix b)[ii][jj]
  rw [Matrix.mul_getElem]
  unfold Matrix.dot Hex.Vector.dotProduct
  let f : Fin n → Rat := fun k => ((coeffs b).row ii)[k] * ((basis b).col jj)[k]
  have hzero : ∀ k : Fin n, i < k.val → f k = 0 := by
    intro k hk
    have hcoeff :
        GramSchmidt.entry (coeffs b) ii k = 0 :=
      coeffs_upper b i k.val hi k.isLt hk
    change ((coeffs b).row ii)[k] * ((basis b).col jj)[k] = 0
    rw [show ((coeffs b).row ii)[k] = 0 from hcoeff]
    grind
  have htrunc := foldl_finRange_eq_prefix_of_zero_above ii f hzero
  change (List.finRange n).foldl (fun acc k => acc + f k) 0 =
    (castIntMatrix b)[ii][jj]
  rw [htrunc]
  rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
  simp only [List.foldl_cons, List.foldl_nil]
  have hprefix :
      (List.finRange i).foldl
        (fun acc (x : Fin i) =>
          acc + f ⟨(Fin.castSucc x).val,
            Nat.lt_of_lt_of_le (Fin.castSucc x).isLt (Nat.succ_le_of_lt hi)⟩) 0 =
      (GramSchmidt.prefixCombination (coeffs b) (basis b) i hi)[jj] := by
    unfold GramSchmidt.prefixCombination GramSchmidt.entry
    let lift : Fin i → Fin n := fun x => ⟨x.val, Nat.lt_trans x.isLt hi⟩
    have hfold :
        ∀ xs : List (Fin i), ∀ accR : Rat, ∀ accV : Vector Rat m,
          accR = accV[jj] →
          xs.foldl
              (fun acc (x : Fin i) =>
                acc + f ⟨(Fin.castSucc x).val,
                  Nat.lt_of_lt_of_le (Fin.castSucc x).isLt (Nat.succ_le_of_lt hi)⟩)
              accR =
            (xs.foldl
              (fun acc (x : Fin i) =>
                acc + GramSchmidt.entry (coeffs b) ii (lift x) • (basis b).row (lift x))
              accV)[jj] := by
      intro xs
      induction xs with
      | nil =>
          intro accR accV hacc
          simp [hacc]
      | cons x xs ih =>
          intro accR accV hacc
          simp only [List.foldl_cons]
          apply ih
          have hstep :
              (accV + GramSchmidt.entry (coeffs b) ii (lift x) •
                  (basis b).row (lift x))[jj] =
                accV[jj] + GramSchmidt.entry (coeffs b) ii (lift x) *
                  ((basis b).row (lift x))[jj] := by
            change (accV + GramSchmidt.entry (coeffs b) ii (lift x) •
                (basis b).row (lift x))[jj.val]'jj.isLt =
              accV[jj.val]'jj.isLt + GramSchmidt.entry (coeffs b) ii (lift x) *
                ((basis b).row (lift x))[jj.val]'jj.isLt
            rw [Vector.getElem_add, Vector.getElem_smul]
            change accV[jj.val]'jj.isLt +
                GramSchmidt.entry (coeffs b) ii (lift x) *
                  ((basis b).row (lift x))[jj.val]'jj.isLt =
              accV[jj.val]'jj.isLt + GramSchmidt.entry (coeffs b) ii (lift x) *
                ((basis b).row (lift x))[jj.val]'jj.isLt
            rfl
          rw [hstep]
          simp [f, lift, GramSchmidt.entry, Matrix.row, Matrix.col, hacc]
    exact hfold (List.finRange i) 0 0 (by simp)
  rw [hprefix]
  have hdiag :
      ((coeffs b).row ii)[ii] = 1 := by
    exact coeffs_diag b i hi
  change (GramSchmidt.prefixCombination (coeffs b) (basis b) i hi)[jj] +
      ((coeffs b).row ii)[ii] * ((basis b).col jj)[ii] =
    (castIntMatrix b)[ii][jj]
  rw [hdiag]
  simp [Matrix.col]
  have hentry' :
      (basis b)[ii][jj] + (GramSchmidt.prefixCombination (coeffs b) (basis b) i hi)[jj] =
        (castIntMatrix b)[ii][jj] := by
    simpa [Matrix.row] using hentry
  change (GramSchmidt.prefixCombination (coeffs b) (basis b) i hi)[jj] +
      (basis b)[ii][jj] = (castIntMatrix b)[ii][jj]
  rw [← hentry']
  exact Lean.Grind.Semiring.add_comm _ _

/-- Integer row combinations reconstruct through the Gram-Schmidt basis after
first combining the Gram-Schmidt coefficient rows. -/
theorem rowCombination_basis_coeffs_reconstruction
    (b : Matrix Int n m) (c : Vector Int n) :
    Vector.map (fun x : Int => (x : Rat)) (Matrix.rowCombination b c) =
      Matrix.rowCombination (basis b)
        (Matrix.rowCombination (coeffs b)
          (Vector.map (fun x : Int => (x : Rat)) c)) := by
  have hcoeff : coeffs b * basis b = castIntMatrix b :=
    coeffs_mul_basis_eq_castIntMatrix b
  apply Vector.ext
  intro j hj
  let jj : Fin m := ⟨j, hj⟩
  change (Vector.map (fun x : Int => (x : Rat)) (Matrix.rowCombination b c))[jj] =
    (Matrix.rowCombination (basis b)
      (Matrix.rowCombination (coeffs b)
        (Vector.map (fun x : Int => (x : Rat)) c)))[jj]
  have hmap :
      (Vector.map (fun x : Int => (x : Rat)) (Matrix.rowCombination b c))[jj] =
        ((Matrix.rowCombination b c)[jj] : Rat) :=
    Vector.getElem_map _ _
  rw [hmap, rowCombination_int_getElem b c jj]
  rw [foldl_int_dot_cast (List.finRange n)
    (fun i : Fin n => b[i][jj]) (fun i : Fin n => c[i]) 0]
  have hleft :
      (List.finRange n).foldl
        (fun acc i => acc + ((b[i][jj] : Int) : Rat) *
          ((c[i] : Int) : Rat)) ((0 : Int) : Rat) =
      (Matrix.rowCombination (castIntMatrix b)
        (Vector.map (fun x : Int => (x : Rat)) c))[jj] := by
    rw [show ((0 : Int) : Rat) = 0 by norm_cast]
    show _ = (Matrix.transpose (castIntMatrix b) *
        Vector.map (fun x : Int => (x : Rat)) c)[jj]
    rw [Matrix.mulVec_getElem]
    simp [Matrix.dot, Hex.Vector.dotProduct, Matrix.row, Matrix.transpose,
      Matrix.col, castIntMatrix]
  rw [hleft]
  rw [← hcoeff]
  change ((Matrix.transpose (coeffs b * basis b)) *
      Vector.map (fun x : Int => (x : Rat)) c)[jj] =
    (Matrix.transpose (basis b) *
      (Matrix.transpose (coeffs b) *
        Vector.map (fun x : Int => (x : Rat)) c))[jj]
  rw [Matrix.transpose_mul_of_mul_comm Lean.Grind.CommSemiring.mul_comm]
  rw [Matrix.mul_assoc_vec]

private theorem exists_highest_nonzero_coeff_in_list
    (c : Vector Int n) (xs : List (Fin n))
    (hne : ∃ i : Fin n, i ∈ xs ∧ c[i] ≠ 0) :
    ∃ k : Fin n, k ∈ xs ∧ c[k] ≠ 0 ∧
      ∀ j : Fin n, j ∈ xs → k.val < j.val → c[j] = 0 := by
  induction xs with
  | nil =>
      rcases hne with ⟨_, hi, _⟩
      cases hi
  | cons x xs ih =>
      by_cases htail : ∃ i : Fin n, i ∈ xs ∧ c[i] ≠ 0
      · rcases ih htail with ⟨k, hk_mem, hck, hmax⟩
        by_cases hx : c[x] ≠ 0
        · by_cases hkx : k.val < x.val
          · refine ⟨x, by simp, hx, ?_⟩
            intro j hj hxj
            simp at hj
            rcases hj with rfl | hjtail
            · omega
            · have hkj : k.val < j.val := by omega
              exact hmax j hjtail hkj
          · refine ⟨k, by simp [hk_mem], hck, ?_⟩
            intro j hj hkj
            simp at hj
            rcases hj with rfl | hjtail
            · exact False.elim (hkx hkj)
            · exact hmax j hjtail hkj
        · refine ⟨k, by simp [hk_mem], hck, ?_⟩
          intro j hj hkj
          simp at hj
          rcases hj with rfl | hjtail
          · by_cases hx0 : c[j] = 0
            · exact hx0
            · exact False.elim (hx hx0)
          · exact hmax j hjtail hkj
      · have hx : c[x] ≠ 0 := by
          rcases hne with ⟨i, hi, hci⟩
          simp at hi
          rcases hi with rfl | hitail
          · exact hci
          · exact False.elim (htail ⟨i, hitail, hci⟩)
        refine ⟨x, by simp, hx, ?_⟩
        intro j hj hxj
        simp at hj
        rcases hj with rfl | hjtail
        · omega
        · by_cases hj0 : c[j] = 0
          · exact hj0
          · exact False.elim (htail ⟨j, hjtail, hj0⟩)

private theorem exists_highest_nonzero_coeff
    (c : Vector Int n) (hne : ∃ i : Fin n, c[i] ≠ 0) :
    ∃ k : Fin n, c[k] ≠ 0 ∧ ∀ j : Fin n, k.val < j.val → c[j] = 0 := by
  have hmem : ∃ i : Fin n, i ∈ List.finRange n ∧ c[i] ≠ 0 := by
    rcases hne with ⟨i, hi⟩
    exact ⟨i, List.mem_finRange i, hi⟩
  rcases exists_highest_nonzero_coeff_in_list c (List.finRange n) hmem with
    ⟨k, _hk_mem, hck, hmax⟩
  exact ⟨k, hck, fun j hj => hmax j (List.mem_finRange j) hj⟩

private theorem normSq_map_intCast (v : Vector Int m) :
    Vector.normSq (Vector.map (fun x : Int => (x : Rat)) v) =
      ((Vector.normSq v : Int) : Rat) := by
  simpa [Vector.normSq, Hex.Vector.normSq, Matrix.dot, Hex.Vector.dotProduct]
    using (foldl_int_dot_cast (List.finRange m)
      (fun i : Fin m => v[i]) (fun i : Fin m => v[i]) 0).symm

theorem normSq_latticeVec_ge_min_basis_normSq
    (b : Matrix Int n m) (_hli : independent b)
    (v : Vector Int m) (hv : memLattice b v) (hv' : v ≠ 0) :
    ∃ i : Fin n,
      Vector.normSq ((basis b).row i) ≤ ((Vector.normSq v : Int) : Rat) := by
  rcases hv with ⟨c, hcv⟩
  have hc_nonzero : ∃ i : Fin n, c[i] ≠ 0 := by
    by_cases h : ∃ i : Fin n, c[i] ≠ 0
    · exact h
    · have hc_zero : c = 0 := by
        apply Vector.ext
        intro i hi
        let ii : Fin n := ⟨i, hi⟩
        by_cases hci : c[ii] = 0
        · simpa [ii] using hci
        · exact False.elim (h ⟨ii, hci⟩)
      have hv_zero : v = 0 := by
        rw [← hcv, hc_zero]
        simp [Matrix.rowCombination]
      exact False.elim (hv' hv_zero)
  rcases exists_highest_nonzero_coeff c hc_nonzero with ⟨k, hck, hzero_above⟩
  let d : Vector Rat n :=
    Matrix.rowCombination (coeffs b) (Vector.map (fun x : Int => (x : Rat)) c)
  have hcoeff_sq : (1 : Rat) ≤ d[k] * d[k] := by
    have htop :
        d[k] = (c[k] : Rat) := by
      dsimp [d]
      exact rowCombination_coeffs_apply_eq_of_zero_above b c k hzero_above
    rw [htop]
    exact GramSchmidt.one_le_intCast_mul_self_of_ne_zero c[k] hck
  refine ⟨k, ?_⟩
  have horth : ∀ i j : Fin n, i ≠ j →
      Matrix.dot ((basis b).row i) ((basis b).row j) = 0 := by
    intro i j hij
    exact basis_orthogonal b i.val j.val i.isLt j.isLt (by
      intro hval
      exact hij (Fin.ext hval))
  have hle :
      Vector.normSq ((basis b).row k) ≤
        Vector.normSq (Matrix.rowCombination (basis b) d) :=
    GramSchmidt.rowCombination_normSq_ge_of_orthogonal_coeff_sq_ge_one
      (rows := basis b) (coeffs := d) (k := k) horth hcoeff_sq
  have hrec :
      Vector.map (fun x : Int => (x : Rat)) v =
        Matrix.rowCombination (basis b) d := by
    rw [← hcv]
    dsimp [d]
    exact rowCombination_basis_coeffs_reconstruction b c
  have hnorm :
      Vector.normSq (Matrix.rowCombination (basis b) d) =
        ((Vector.normSq v : Int) : Rat) := by
    rw [← hrec, normSq_map_intCast]
  rw [← hnorm]
  exact hle

/-! ### Dot-product symmetry support -/

private theorem foldl_dot_comm_int {n' : Nat} (xs : List (Fin n'))
    (u v : Vector Int n') (accU accV : Int) (hacc : accU = accV) :
    xs.foldl (fun acc i => acc + u[i] * v[i]) accU =
      xs.foldl (fun acc i => acc + v[i] * u[i]) accV := by
  induction xs generalizing accU accV with
  | nil =>
      simp [hacc]
  | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih
      grind

/-- The dot product of integer vectors is commutative. -/
private theorem dot_comm_int {n' : Nat} (u v : Vector Int n') :
    Matrix.dot u v = Matrix.dot v u := by
  simpa [Matrix.dot, Hex.Vector.dotProduct] using
    foldl_dot_comm_int (xs := List.finRange n') (u := u) (v := v)
      (accU := 0) (accV := 0) rfl

/-- The integer Gram matrix is symmetric: each entry equals the entry at the
swapped index. Consumed by the no-pivot Bareiss symmetry/transpose argument for
bordered minors of `gramMatrix b`. -/
private theorem gramMatrix_symm (b : Matrix Int n m) (a c : Fin n) :
    (Matrix.gramMatrix b)[a][c] = (Matrix.gramMatrix b)[c][a] := by
  show (Matrix.ofFn fun i j => Hex.Vector.dotProduct
        (Matrix.row b i) (Matrix.row b j))[a][c]
    = (Matrix.ofFn fun i j => Hex.Vector.dotProduct
        (Matrix.row b i) (Matrix.row b j))[c][a]
  simp [Matrix.ofFn, Vector.getElem_ofFn]
  exact dot_comm_int _ _

/-- The Cramer determinant matrix for the scaled Gram-Schmidt coefficient
`(i, j)` (with `j < i`) is the bordered minor of `gramMatrix b` at level `j`
with the border row index taken to be `j` and the border column index taken
to be `i`. This is the definitional equation between
`GramSchmidt.scaledCoeffMatrix` and the bordered-minor machinery in
`HexMatrix.Bareiss`. -/
theorem scaledCoeffMatrix_eq_borderedMinor
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) :
    GramSchmidt.scaledCoeffMatrix b i j hji =
      Matrix.borderedMinor (Matrix.gramMatrix b) j.val
        (Nat.lt_trans hji i.isLt)
        ⟨j.val, Nat.lt_trans hji i.isLt⟩ i := by
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  let pp : Fin (j.val + 1) := ⟨r, hr⟩
  let cc : Fin (j.val + 1) := ⟨c, hc⟩
  show (GramSchmidt.scaledCoeffMatrix b i j hji)[pp][cc] =
    (Matrix.borderedMinor (Matrix.gramMatrix b) j.val
        (Nat.lt_trans hji i.isLt)
        ⟨j.val, Nat.lt_trans hji i.isLt⟩ i)[pp][cc]
  -- Case split on whether the column index is the border (= j.val) or interior.
  by_cases hcj : cc.val < j.val
  · -- Interior column: both sides are `gramMatrix[r'][c']` with the
    -- lifted-to-`Fin n` indices, since the bordered-minor `r` lookup falls into
    -- the lt branch when `pp.val < j.val` and into the border (= j) row when
    -- `pp.val = j.val`. Splitting on the row case mirrors the bordered minor.
    by_cases hrj : pp.val < j.val
    · have h_sc : (GramSchmidt.scaledCoeffMatrix b i j hji)[pp][cc] =
          Matrix.dot
            (Matrix.row b ⟨pp.val, Nat.lt_of_lt_of_le pp.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt))⟩)
            (Matrix.row b ⟨cc.val, Nat.lt_of_lt_of_le cc.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt))⟩) := by
        have hcc_ne : cc.val ≠ j.val := Nat.ne_of_lt hcj
        simp [GramSchmidt.scaledCoeffMatrix, Matrix.ofFn, GramSchmidt.liftFinLE, hcc_ne]
      have h_bm : (Matrix.borderedMinor (Matrix.gramMatrix b) j.val
            (Nat.lt_trans hji i.isLt)
            ⟨j.val, Nat.lt_trans hji i.isLt⟩ i)[pp][cc] =
          (Matrix.gramMatrix b)[
            (⟨pp.val, Nat.lt_trans hrj (Nat.lt_trans hji i.isLt)⟩ : Fin n)][
            (⟨cc.val, Nat.lt_trans hcj (Nat.lt_trans hji i.isLt)⟩ : Fin n)] := by
        rw [Matrix.borderedMinor_entry_lt_lt (Matrix.gramMatrix b) j.val
          (Nat.lt_trans hji i.isLt) ⟨j.val, Nat.lt_trans hji i.isLt⟩ i pp cc hrj hcj]
      rw [h_sc, h_bm]
      simp [Matrix.gramMatrix, Matrix.ofFn, Vector.getElem_ofFn, Matrix.dot]
    · -- pp.val = j.val (since not < j.val and bounded by j.val + 1).
      have hpr : pp.val = j.val :=
        Nat.le_antisymm (Nat.lt_succ_iff.mp pp.isLt) (Nat.le_of_not_lt hrj)
      have h_sc : (GramSchmidt.scaledCoeffMatrix b i j hji)[pp][cc] =
          Matrix.dot
            (Matrix.row b ⟨pp.val, Nat.lt_of_lt_of_le pp.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt))⟩)
            (Matrix.row b ⟨cc.val, Nat.lt_of_lt_of_le cc.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt))⟩) := by
        have hcc_ne : cc.val ≠ j.val := Nat.ne_of_lt hcj
        simp [GramSchmidt.scaledCoeffMatrix, Matrix.ofFn, GramSchmidt.liftFinLE, hcc_ne]
      have h_bm : (Matrix.borderedMinor (Matrix.gramMatrix b) j.val
            (Nat.lt_trans hji i.isLt)
            ⟨j.val, Nat.lt_trans hji i.isLt⟩ i)[pp][cc] =
          (Matrix.gramMatrix b)[(⟨j.val, Nat.lt_trans hji i.isLt⟩ : Fin n)][
            (⟨cc.val, Nat.lt_trans hcj (Nat.lt_trans hji i.isLt)⟩ : Fin n)] := by
        have hpr_not : ¬ pp.val < j.val := Nat.not_lt.mpr (Nat.le_of_eq hpr.symm)
        simp [Matrix.borderedMinor, Matrix.ofFn, Vector.getElem_ofFn, hpr_not, hcj]
      rw [h_sc, h_bm]
      simp [Matrix.gramMatrix, Matrix.ofFn, Vector.getElem_ofFn, Matrix.dot]
      congr 2
      exact Fin.ext hpr
  · -- Border column: cc.val = j.val.
    have hcj_eq : cc.val = j.val :=
      Nat.le_antisymm (Nat.lt_succ_iff.mp cc.isLt) (Nat.le_of_not_lt hcj)
    by_cases hrj : pp.val < j.val
    · have h_sc : (GramSchmidt.scaledCoeffMatrix b i j hji)[pp][cc] =
          Matrix.dot
            (Matrix.row b ⟨pp.val, Nat.lt_of_lt_of_le pp.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt))⟩)
            (Matrix.row b i) := by
        simp [GramSchmidt.scaledCoeffMatrix, Matrix.ofFn, GramSchmidt.liftFinLE, hcj_eq]
      have h_bm : (Matrix.borderedMinor (Matrix.gramMatrix b) j.val
            (Nat.lt_trans hji i.isLt)
            ⟨j.val, Nat.lt_trans hji i.isLt⟩ i)[pp][cc] =
          (Matrix.gramMatrix b)[
            (⟨pp.val, Nat.lt_trans hrj (Nat.lt_trans hji i.isLt)⟩ : Fin n)][i] := by
        simp [Matrix.borderedMinor, Matrix.ofFn, Vector.getElem_ofFn, hrj, hcj]
      rw [h_sc, h_bm]
      simp [Matrix.gramMatrix, Matrix.ofFn, Vector.getElem_ofFn, Matrix.dot]
    · -- pp.val = j.val and cc.val = j.val: corner case.
      have hpr_eq : pp.val = j.val :=
        Nat.le_antisymm (Nat.lt_succ_iff.mp pp.isLt) (Nat.le_of_not_lt hrj)
      have h_sc : (GramSchmidt.scaledCoeffMatrix b i j hji)[pp][cc] =
          Matrix.dot
            (Matrix.row b ⟨pp.val, Nat.lt_of_lt_of_le pp.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hji i.isLt))⟩)
            (Matrix.row b i) := by
        simp [GramSchmidt.scaledCoeffMatrix, Matrix.ofFn, GramSchmidt.liftFinLE, hcj_eq]
      have h_bm : (Matrix.borderedMinor (Matrix.gramMatrix b) j.val
            (Nat.lt_trans hji i.isLt)
            ⟨j.val, Nat.lt_trans hji i.isLt⟩ i)[pp][cc] =
          (Matrix.gramMatrix b)[(⟨j.val, Nat.lt_trans hji i.isLt⟩ : Fin n)][i] := by
        have hpr_not : ¬ pp.val < j.val := hrj
        simp [Matrix.borderedMinor, Matrix.ofFn, Vector.getElem_ofFn, hpr_not, hcj]
      rw [h_sc, h_bm]
      simp [Matrix.gramMatrix, Matrix.ofFn, Vector.getElem_ofFn, Matrix.dot]
      congr 2
      exact Fin.ext hpr_eq

/-- The no-pivot Bareiss-style trailing value on `scaledCoeffMatrix b i j hji`
agrees with the value on the bordered minor of `gramMatrix b` whose border
row/column are swapped. The proof composes the symmetry of `gramMatrix` (via
`noPivotLoop_borderedMinor_swap_at_trailing`) with the definitional identity
`scaledCoeffMatrix_eq_borderedMinor`. -/
private theorem noPivotLoop_scaledCoeffMatrix_eq_borderedMinor_at_trailing
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) :
    (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState
          (GramSchmidt.scaledCoeffMatrix b i j hji))).matrix[
          Fin.last j.val][Fin.last j.val] =
    (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState
          (Matrix.borderedMinor (Matrix.gramMatrix b) j.val
            (Nat.lt_trans hji i.isLt) i j))).matrix[
          Fin.last j.val][Fin.last j.val] := by
  rw [scaledCoeffMatrix_eq_borderedMinor b i j hji]
  exact noPivotLoop_borderedMinor_swap_at_trailing
    (Matrix.gramMatrix b) (gramMatrix_symm (b := b))
    j.val (Nat.lt_trans hji i.isLt)
    ⟨j.val, Nat.lt_trans hji i.isLt⟩ i
    (Nat.le_refl _) (Nat.le_of_lt hji)

/-- Non-singular top-level composite: when the no-pivot Bareiss pass over the
full Gram matrix has not recorded a singular step before reaching column `j`,
the executable scaled-coefficient array entry below the diagonal at `(i, j)`
matches the trailing entry of the no-pivot Bareiss-style loop on the
corresponding Cramer determinant matrix `scaledCoeffMatrix b i j hji`. This
composes `scaledCoeffArrayLoop_lower_matches_target_column` (from #4103),
`noPivotLoop_full_eq_borderedMinor_at_trailing` (from #4028), and the
symmetry/transpose equation `noPivotLoop_scaledCoeffMatrix_eq_borderedMinor_at_trailing`. -/
theorem scaledCoeffRows_lower_eq_noPivotLoop_scaledCoeffMatrix
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val)
    (h_nonsing :
      (Matrix.noPivotLoop j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none) :
    getArrayEntry (scaledCoeffRows b) i.val j.val =
      (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState
          (GramSchmidt.scaledCoeffMatrix b i j hji))).matrix[
        Fin.last j.val][Fin.last j.val] := by
  -- Step 1: top-level state-level invariant via the non-singular target-column lemma.
  have h_target_nonsing :
      (Matrix.noPivotLoop (j.val - 0)
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = none := by
    simpa using h_nonsing
  have h_lower :=
    scaledCoeffArrayLoop_lower_matches_target_column
      (state_array :=
        { step := 0
          matrix := gramRows b
          coeffs := zeroRows n
          prevPivot := 1 })
      (state_matrix := Matrix.noPivotInitialState (Matrix.gramMatrix b))
      (by rfl) (rowsToMatrix_gramRows b) (by rfl)
      (gramRows_size b) (gramRows_row_size b)
      (zeroRows_size n) (zeroRows_row_size n)
      n i j (Nat.zero_le _) hji
      (by have := i.isLt; omega) h_target_nonsing
  have h_state_level :
      getArrayEntry (scaledCoeffRows b) i.val j.val =
        (Matrix.noPivotLoop j.val
          (Matrix.noPivotInitialState (Matrix.gramMatrix b))).matrix[i][j] := by
    show getArrayEntry
        (scaledCoeffArrayLoop n n
            { step := 0, matrix := gramRows b, coeffs := zeroRows n,
              prevPivot := 1 }).coeffs i.val j.val = _
    have h_step_eq : (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step = 0 := rfl
    have h_sub : j.val - (Matrix.noPivotInitialState (Matrix.gramMatrix b)).step = j.val := by
      rw [h_step_eq]; omega
    rw [h_lower, h_sub]
  rw [h_state_level]
  -- Step 2: bordered-minor sync at (row=i, col=j).
  have h_bm :=
    (noPivotLoop_full_eq_borderedMinor_at_trailing (Matrix.gramMatrix b) j.val
      (Nat.lt_trans hji i.isLt) i j (Nat.le_of_lt hji) (Nat.le_refl _)).1
  rw [h_bm]
  -- Step 3: symmetry/transpose equation to `scaledCoeffMatrix`.
  exact
    (noPivotLoop_scaledCoeffMatrix_eq_borderedMinor_at_trailing b i j hji).symm

/-- Singular dual of `scaledCoeffRows_lower_eq_noPivotLoop_scaledCoeffMatrix`.
When the no-pivot Bareiss pass over the full Gram matrix records an early
singular step before reaching column `j`, the integral scaled Gram-Schmidt
coefficient below the diagonal at `(i, j)` is zero. The array loop halts at
the recorded singular column and the target column is never written. -/
theorem scaledCoeffs_eq_zero_of_singularStep_lt
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val)
    (s : Nat)
    (h_sing : (Matrix.noPivotLoop j.val
        (Matrix.noPivotInitialState (Matrix.gramMatrix b))).singularStep = some s)
    (hsj : s < j.val) :
    GramSchmidt.entry (scaledCoeffs b) i j = 0 := by
  sorry


private theorem rowSwap_row_eq_of_ne_int {n' m' : Nat}
    (M : Matrix Int n' m') (i j r : Fin n')
    (hri : r.val ≠ i.val) (hrj : r.val ≠ j.val) :
    (Matrix.rowSwap M i j)[r] = M[r] := by
  apply Vector.ext
  intro c hc
  have hr_ne_j : r ≠ j := fun h => hrj (congrArg Fin.val h)
  have hr_ne_i : r ≠ i := fun h => hri (congrArg Fin.val h)
  have hget := Matrix.rowSwap_getElem M i j r ⟨c, hc⟩
  rw [if_neg hr_ne_j, if_neg hr_ne_i] at hget
  simpa [Matrix.row] using hget

private theorem rowSwap_row_left_int {n' m' : Nat}
    (M : Matrix Int n' m') (i j : Fin n') :
    (Matrix.rowSwap M i j)[i] = M[j] := by
  apply Vector.ext
  intro c hc
  by_cases hij : i = j
  · subst j
    have hget := Matrix.rowSwap_getElem M i i i ⟨c, hc⟩
    rw [if_pos rfl] at hget
    exact hget
  · have hget := Matrix.rowSwap_getElem M i j i ⟨c, hc⟩
    rw [if_neg hij, if_pos rfl] at hget
    simpa [Matrix.row] using hget

private theorem rowSwap_row_right_int {n' m' : Nat}
    (M : Matrix Int n' m') (i j : Fin n') :
    (Matrix.rowSwap M i j)[j] = M[i] := by
  apply Vector.ext
  intro c hc
  have hget := Matrix.rowSwap_getElem M i j j ⟨c, hc⟩
  rw [if_pos rfl] at hget
  simpa [Matrix.row] using hget

private theorem rowSwap_getRow_eq_of_ne_val_int {n' m' : Nat}
    (M : Matrix Int n' m') (i j : Fin n') (r : Nat) (hr : r < n')
    (hri : r ≠ i.val) (hrj : r ≠ j.val) :
    (Matrix.rowSwap M i j)[r]'hr = M[r]'hr := by
  let rf : Fin n' := ⟨r, hr⟩
  change (Matrix.rowSwap M i j)[rf] = M[rf]
  exact rowSwap_row_eq_of_ne_int M i j rf hri hrj

private theorem rowSwap_getRow_left_val_int {n' m' : Nat}
    (M : Matrix Int n' m') (i j : Fin n') (hr : i.val < n') :
    (Matrix.rowSwap M i j)[i.val]'hr = M[j] := by
  apply Vector.ext
  intro c hc
  let ii : Fin n' := ⟨i.val, hr⟩
  change (Matrix.rowSwap M i j)[ii][c] = M[j][c]
  have hget := Matrix.rowSwap_getElem M i j ii ⟨c, hc⟩
  by_cases hij : ii = j
  · have hij' : i = j := by
      apply Fin.ext
      simpa [ii] using congrArg Fin.val hij
    rw [if_pos hij] at hget
    simpa [Matrix.row, hij'] using hget
  · have hii : ii = i := Fin.ext rfl
    rw [if_neg hij, if_pos hii] at hget
    simpa [Matrix.row] using hget

private theorem rowSwap_getRow_right_val_int {n' m' : Nat}
    (M : Matrix Int n' m') (i j : Fin n') (hr : j.val < n') :
    (Matrix.rowSwap M i j)[j.val]'hr = M[i] := by
  apply Vector.ext
  intro c hc
  let jj : Fin n' := ⟨j.val, hr⟩
  change (Matrix.rowSwap M i j)[jj][c] = M[i][c]
  have hjj : jj = j := Fin.ext rfl
  have hget := Matrix.rowSwap_getElem M i j jj ⟨c, hc⟩
  rw [if_pos hjj] at hget
  simpa [Matrix.row] using hget

theorem scaledCoeffMatrix_rowSwap_adjacent_pivot_transpose
    (b : Matrix Int n m) (km1 k : Fin n) (hkm1 : km1.val + 1 = k.val)
    (hkm1k : km1.val < k.val) :
    GramSchmidt.scaledCoeffMatrix (Matrix.rowSwap b km1 k) k km1 hkm1k =
      (GramSchmidt.scaledCoeffMatrix b k km1 hkm1k).transpose := by
  let t := km1.val + 1
  let ht : t ≤ n := Nat.succ_le_of_lt km1.isLt
  let last : Fin t := ⟨km1.val, Nat.lt_succ_self km1.val⟩
  apply Vector.ext
  intro r hr
  apply Vector.ext
  intro c hc
  let p : Fin t := ⟨r, hr⟩
  let q : Fin t := ⟨c, hc⟩
  change
    (GramSchmidt.scaledCoeffMatrix (Matrix.rowSwap b km1 k) k km1 hkm1k)[p][q] =
      ((GramSchmidt.scaledCoeffMatrix b k km1 hkm1k).transpose)[p][q]
  have hp_lt_k : p.val < k.val := by
    dsimp [p, t]
    omega
  have hq_lt_k : q.val < k.val := by
    dsimp [q, t]
    omega
  have hp_ne_k : (GramSchmidt.liftFinLE p ht).val ≠ k.val := by
    dsimp [GramSchmidt.liftFinLE, p, t]
    omega
  have hq_ne_k : (GramSchmidt.liftFinLE q ht).val ≠ k.val := by
    dsimp [GramSchmidt.liftFinLE, q, t]
    omega
  have hlast_val : last.val = km1.val := rfl
  by_cases hq_last : q = last
  · have hq_val : q.val = km1.val := by
      simpa [last] using congrArg Fin.val hq_last
    by_cases hp_last : p = last
    · have hp_lift : GramSchmidt.liftFinLE p ht = km1 := by
        apply Fin.ext
        simpa [last, GramSchmidt.liftFinLE] using congrArg Fin.val hp_last
      have hq_lift : GramSchmidt.liftFinLE q ht = km1 := by
        apply Fin.ext
        simpa [last, GramSchmidt.liftFinLE] using congrArg Fin.val hq_last
      dsimp [GramSchmidt.scaledCoeffMatrix, Matrix.transpose, Matrix.col,
        Matrix.row, Matrix.ofFn]
      repeat rw [Vector.getElem_ofFn]
      rw [if_pos hq_val]
      rw [if_pos (by simpa [last] using congrArg Fin.val hp_last)]
      rw [rowSwap_getRow_right_val_int]
      rw [show (GramSchmidt.liftFinLE (⟨p.val, hr⟩ : Fin t) _) = km1 by
        apply Fin.ext
        dsimp [GramSchmidt.liftFinLE]
        omega]
      rw [rowSwap_getRow_left_val_int]
      rw [show (GramSchmidt.liftFinLE (⟨q.val, hc⟩ : Fin t) _) = km1 by
        apply Fin.ext
        dsimp [GramSchmidt.liftFinLE]
        omega]
      exact dot_comm_int _ _
    · have hp_ne_km1 : (GramSchmidt.liftFinLE p ht).val ≠ km1.val := by
        intro h
        exact hp_last (Fin.ext (by simpa [last, GramSchmidt.liftFinLE] using h))
      have hq_lift : GramSchmidt.liftFinLE q ht = km1 := by
        apply Fin.ext
        simpa [last, GramSchmidt.liftFinLE] using congrArg Fin.val hq_last
      have hp_val_ne : p.val ≠ km1.val := by
        intro h
        exact hp_last (Fin.ext (by simpa [last] using h))
      dsimp [GramSchmidt.scaledCoeffMatrix, Matrix.transpose, Matrix.col,
        Matrix.row, Matrix.ofFn]
      repeat rw [Vector.getElem_ofFn]
      rw [if_pos hq_val]
      rw [if_neg hp_val_ne]
      rw [rowSwap_getRow_right_val_int]
      rw [rowSwap_getRow_eq_of_ne_val_int]
      · rw [show (GramSchmidt.liftFinLE q _) = km1 by
          apply Fin.ext
          dsimp [GramSchmidt.liftFinLE]
          omega]
        exact dot_comm_int _ _
      · dsimp [GramSchmidt.liftFinLE]
        omega
      · dsimp [GramSchmidt.liftFinLE]
        omega
  · have hq_ne_val : q.val ≠ km1.val := by
      intro h
      exact hq_last (Fin.ext (by simpa [last] using h))
    by_cases hp_last : p = last
    · have hp_val : p.val = km1.val := by
        simpa [last] using congrArg Fin.val hp_last
      have hp_lift : GramSchmidt.liftFinLE p ht = km1 := by
        apply Fin.ext
        simpa [last, GramSchmidt.liftFinLE] using congrArg Fin.val hp_last
      have hq_ne_km1 : (GramSchmidt.liftFinLE q ht).val ≠ km1.val := by
        intro h
        exact hq_ne_val (by simpa [GramSchmidt.liftFinLE] using h)
      dsimp [GramSchmidt.scaledCoeffMatrix, Matrix.transpose, Matrix.col,
        Matrix.row, Matrix.ofFn]
      repeat rw [Vector.getElem_ofFn]
      rw [if_neg hq_ne_val]
      rw [if_pos hp_val]
      rw [show (GramSchmidt.liftFinLE (⟨p.val, hr⟩ : Fin t) _) = km1 by
        apply Fin.ext
        dsimp [GramSchmidt.liftFinLE]
        omega]
      rw [rowSwap_getRow_left_val_int]
      rw [rowSwap_getRow_eq_of_ne_val_int]
      · exact dot_comm_int _ _
      · dsimp [GramSchmidt.liftFinLE]
        omega
      · dsimp [GramSchmidt.liftFinLE]
        omega
    · have hp_ne_val : p.val ≠ km1.val := by
        intro h
        exact hp_last (Fin.ext (by simpa [last] using h))
      have hp_ne_km1 : (GramSchmidt.liftFinLE p ht).val ≠ km1.val := by
        intro h
        exact hp_ne_val (by simpa [GramSchmidt.liftFinLE] using h)
      have hq_ne_km1 : (GramSchmidt.liftFinLE q ht).val ≠ km1.val := by
        intro h
        exact hq_ne_val (by simpa [GramSchmidt.liftFinLE] using h)
      dsimp [GramSchmidt.scaledCoeffMatrix, Matrix.transpose, Matrix.col,
        Matrix.row, Matrix.ofFn]
      repeat rw [Vector.getElem_ofFn]
      rw [if_neg hq_ne_val]
      rw [if_neg hp_ne_val]
      rw [rowSwap_getRow_eq_of_ne_val_int]
      · rw [rowSwap_getRow_eq_of_ne_val_int]
        · exact dot_comm_int _ _
        · dsimp [GramSchmidt.liftFinLE]
          omega
        · dsimp [GramSchmidt.liftFinLE]
          omega
      · dsimp [GramSchmidt.liftFinLE]
        omega
      · dsimp [GramSchmidt.liftFinLE]
        omega



end GramSchmidt.Int

namespace GramSchmidt.Rat

/-- The `k`-th Gram determinant for a rational input matrix.

This remains Mathlib-free API: it is the direct Hex determinant definition used
by rational Gram-Schmidt callers, not a theorem identifying an executable Hex
output with a Leibniz determinant. -/
def gramDet (b : Matrix Rat n m) (k : Nat) (hk : k ≤ n) : Rat :=
  Matrix.det (GramSchmidt.leadingGramMatrixRat b k hk)

end GramSchmidt.Rat

end Hex
