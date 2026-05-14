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
private def liftFinLE (i : Fin k) (hk : k ≤ n) : Fin n :=
  ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩

/-- Leading principal Gram matrix of the first `k` rows of an integer basis. -/
def leadingGramMatrixInt (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) : Matrix Int k k :=
  Matrix.ofFn fun i j =>
    Matrix.dot (b.row (liftFinLE i hk)) (b.row (liftFinLE j hk))

/-- The Gram-Schmidt leading Gram matrix is the leading prefix of the full
Gram matrix. This is the shape bridge between the public `gramDet` API and
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
private def gramDetVecEntry (data : Matrix.BareissData n) (k : Fin (n + 1)) : Nat :=
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
private theorem gramDetVecEntry_noPivot_eq_zero_of_singularStep_lt
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

@[inline] private def getArrayEntry (rows : Array (Array Int)) (row col : Nat) : Int :=
  rows[row]![col]!

private def zeroRows (n : Nat) : Array (Array Int) :=
  (Array.range n).map fun _ => (Array.range n).map fun _ => 0

private def gramRows (b : Matrix Int n m) : Array (Array Int) :=
  (Array.range n).map fun row =>
    (Array.range n).map fun col =>
      if hrow : row < n then
        if hcol : col < n then
          let i : Fin n := ⟨row, hrow⟩
          let j : Fin n := ⟨col, hcol⟩
          Matrix.dot (b.row i) (b.row j)
        else
          0
      else
        0

private theorem getArrayEntry_gramRows (b : Matrix Int n m) (i j : Fin n) :
    getArrayEntry (gramRows b) i.val j.val = (Matrix.gramMatrix b)[i][j] := by
  simp [getArrayEntry, gramRows, Matrix.gramMatrix, Matrix.dot, Matrix.ofFn]

private def rowsToMatrix (rows : Array (Array Int)) (n : Nat) : Matrix Int n n :=
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
    · simp [Array.getElem?_setIfInBounds, hne]
    · simp [Array.setIfInBounds, hbound]

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
    for i in [k + 1:n] do
      let sourceRow := rows[i]!
      let entryIK := sourceRow[k]!
      let mut nextRow := sourceRow.set! k 0
      for j in [k + 1:n] do
        let value :=
          (pivot * sourceRow[j]! - entryIK * getArrayEntry rows k j) / prevPivot
        nextRow := nextRow.set! j value
      next := next.set! i nextRow
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
  rw [getElem!_foldl_set!_of_notMem _ _ _ _ hnot]

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
  rw [getElem!_foldl_set!_of_notMem _ _ _ _ hnot]

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
            ((pivot * rows[r]![j]! - rows[r]![k]! * getArrayEntry rows k j) / prevPivot))
        (rows[r]!.set! k 0) := by
  unfold stepScaledRows
  simp [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    -Array.set!_eq_setIfInBounds]
  have hmem : r ∈ List.range' (k + 1) (n - (k + 1)) := by
    rw [List.mem_range']
    exact ⟨r - (k + 1), by omega, by omega⟩
  have hnodup : (List.range' (k + 1) (n - (k + 1))).Nodup := List.nodup_range'
  rw [getElem!_foldl_set!_of_mem_nodup _ _ _ _ hmem hnodup hrows]

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
  rw [getElem!_foldl_set!_of_notMem _ _ _ _ hnot]
  grind

/-- Trailing-column entries of `stepScaledRows` are the fraction-free
Bareiss-style update written by the inner sweep. -/
private theorem getArrayEntry_stepScaledRows_trailing
    (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int)
    (r c : Nat) (hkr : k < r) (hr : r < n) (hkc : k < c) (hc : c < n)
    (hrows : r < rows.size) (hcols : c < rows[r]!.size) :
    getArrayEntry (stepScaledRows rows n k pivot prevPivot) r c =
      (pivot * rows[r]![c]! - rows[r]![k]! * getArrayEntry rows k c) / prevPivot := by
  show
      (stepScaledRows rows n k pivot prevPivot)[r]![c]! =
        (pivot * rows[r]![c]! - rows[r]![k]! * getArrayEntry rows k c) / prevPivot
  rw [stepScaledRows_row_at_trailing rows n k pivot prevPivot r hkr hr hrows]
  have hmem : c ∈ List.range' (k + 1) (n - (k + 1)) := by
    rw [List.mem_range']
    exact ⟨c - (k + 1), by omega, by omega⟩
  have hnodup : (List.range' (k + 1) (n - (k + 1))).Nodup := List.nodup_range'
  have hbound : c < (rows[r]!.set! k 0).size := by
    simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, hcols]
  rw [getElem!_foldl_set!_of_mem_nodup _ _ _ _ hmem hnodup hbound]

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
  rw [getElem!_foldl_set!_of_notMem _ _ _ _ hnot]
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
  exact size_foldl_set! _ _ _

/-- Per-entry correspondence between the array-storage `stepScaledRows`
update and the matrix-storage `Matrix.stepMatrix` update. Trailing-block
entries match under exact divisibility, the pivot column clears to zero,
and entries outside the update region are preserved on both sides. The
divisibility hypothesis bridges Lean's `Int` `/` (used inside
`stepScaledRows`) and `Matrix.exactDiv` (used inside `Matrix.stepMatrix`). -/
private theorem getArrayEntry_stepScaledRows_matches_stepMatrix
    {n : Nat} (rows : Array (Array Int)) (M : Matrix Int n n) (k : Nat)
    (pivot prevPivot : Int)
    (hentry : ∀ a b : Fin n, getArrayEntry rows a.val b.val = M[a][b])
    (hsize : rows.size = n)
    (hrowsize : ∀ (a : Nat), a < n → rows[a]!.size = n)
    (i j : Fin n)
    (hdvd : k < i.val → k < j.val →
      prevPivot ∣
        (pivot * getArrayEntry rows i.val j.val -
          getArrayEntry rows i.val k * getArrayEntry rows k j.val)) :
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
      have hdvd' := hdvd hki hkj
      have hdvd_M : prevPivot ∣
          (pivot * M[i][j] -
            M[i][(⟨k, Nat.lt_trans hki i.isLt⟩ : Fin n)] *
              M[(⟨k, Nat.lt_trans hkj j.isLt⟩ : Fin n)][j]) := by
        rw [← hij_eq, ← hcol_eq, ← hrow_eq]; exact hdvd'
      rw [getArrayEntry_stepScaledRows_trailing rows n k pivot prevPivot
            i.val j.val hki i.isLt hkj j.isLt hrows hcols]
      rw [Matrix.stepMatrix_update_eq M k pivot prevPivot i j hki hkj]
      simp only
      rw [Matrix.exactDiv_eq_divExact hdvd_M]
      rw [Int.divExact_eq_ediv hdvd_M]
      show (pivot * getArrayEntry rows i.val j.val -
              getArrayEntry rows i.val k * getArrayEntry rows k j.val) / prevPivot = _
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

/-- Matrix-level correspondence: one `stepScaledRows` array update, viewed
as a matrix via `rowsToMatrix`, equals the corresponding `Matrix.stepMatrix`
update on the matrix view of the same row storage. The hypothesis encodes
the Bareiss exact-divisibility condition that must hold for the array-side
integer division to agree with `Matrix.exactDiv`. -/
private theorem rowsToMatrix_stepScaledRows_eq_stepMatrix_of_dvd
    {n : Nat} (rows : Array (Array Int)) (k : Nat) (pivot prevPivot : Int)
    (hsize : rows.size = n)
    (hrowsize : ∀ (a : Nat), a < n → rows[a]!.size = n)
    (hdvd : ∀ (i j : Fin n), k < i.val → k < j.val →
      prevPivot ∣
        (pivot * getArrayEntry rows i.val j.val -
          getArrayEntry rows i.val k * getArrayEntry rows k j.val)) :
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
      (fun hki hkj => hdvd ⟨i, hi⟩ ⟨j, hj⟩ hki hkj)

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
                matrix := Matrix.stepArray state.matrix n k pivot state.prevPivot
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
                matrix := Matrix.stepArray state.matrix n state.step
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

/-- Run one no-pivot fraction-free Gram elimination and record each scaled
coefficient column immediately before the elimination step zeroes it. -/
private def scaledCoeffRows (b : Matrix Int n m) : Array (Array Int) :=
  let state :=
    scaledCoeffArrayLoop n n
      { step := 0
        matrix := gramRows b
        coeffs := zeroRows n
        prevPivot := 1 }
  state.coeffs

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

/-- Run the shared fraction-free Gram pass once and package both the leading
Gram determinant vector and the scaled Gram-Schmidt coefficient matrix. -/
def data (b : Matrix Int n m) : Data n :=
  let rows := scaledCoeffRows b
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
        -- entry as a function of Fin n to bridge the gap.
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
private theorem noPivotLoop_id_at_singular_fixedpoint
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
private theorem noPivotLoop_add
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
private theorem noPivotLoop_singular_inv
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

/-- The `step` field of a no-pivot Bareiss state never decreases under further
loop iterations. -/
private theorem noPivotLoop_step_monotone
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
private theorem gramDetVecEntry_bareissNoPivot_full_eq_leadingPrefix
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
the last column applies one canonical Bareiss `stepArray` update, advances
`step`, records the new `prevPivot`, and recurses on the remaining fuel. -/
private theorem scaledCoeffArrayLoop_regular_branch (fuel : Nat)
    (state : ScaledCoeffArrayState)
    (hStep : state.step < n) (hNext : state.step + 1 < n)
    (hp : getArrayEntry state.matrix state.step state.step ≠ 0) :
    scaledCoeffArrayLoop n (fuel + 1) state =
      scaledCoeffArrayLoop n fuel
        { step := state.step + 1
          matrix := Matrix.stepArray state.matrix n state.step
            (getArrayEntry state.matrix state.step state.step) state.prevPivot
          coeffs := writeScaledColumn state.coeffs state.matrix n state.step
          prevPivot := getArrayEntry state.matrix state.step state.step } := by
  simp [scaledCoeffArrayLoop, hStep, hNext, hp]

/-- The matrix-side view of a row-storage entry: `getArrayEntry` on the array
matches the matrix-level `[i][j]` lookup under the `rowsToMatrix` bridge. -/
private theorem getArrayEntry_eq_rowsToMatrix
    (rows : Array (Array Int)) (i j : Fin n) :
    getArrayEntry rows i.val j.val = (rowsToMatrix rows n)[i][j] := by
  simp [rowsToMatrix, Matrix.ofFn]

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
        -- Bridge pivot equality between array and matrix views.
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
              matrix := Matrix.stepArray state_array.matrix n state_array.step
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
                (Matrix.stepArray state_array.matrix n state_array.step _ state_array.prevPivot) n =
              Matrix.stepMatrix state_matrix.matrix state_matrix.step _ state_matrix.prevPivot
            rw [rowsToMatrix_stepArray_eq_stepMatrix, h_matrix_eq, h_pivot_array_eq_matrix,
              h_step_eq, h_prev_eq]
          have h_prev_new : new_array.prevPivot = new_matrix.prevPivot := h_pivot_array_eq_matrix
          have h_no_sing_new : new_matrix.singularStep = none := rfl
          have h_array_size_new : new_array.matrix.size = n := Matrix.stepArray_size _ _ _ _ _
          have h_array_rows_size_new : ∀ r, r < n → new_array.matrix[r]!.size = n := by
            intro r hr
            show (Matrix.stepArray state_array.matrix n state_array.step _ _)[r]!.size = n
            unfold Matrix.stepArray
            simp only [Array.getElem!_eq_getD, Array.getD, Array.size_map, Array.size_range]
            simp [hr, Array.size_map, Array.size_range]
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
leading-prefix determinant as the public `gramDet` API at every vector slot. -/
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
private theorem gramDetVecEntry_eq_gramDet
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

/-- The fraction-free scaled-coefficient loop records, below the diagonal, the
Bareiss determinant of the Cramer matrix for the corresponding
Gram-Schmidt coefficient. This is the executable-array invariant needed to
connect `scaledCoeffRows` with the determinant formula in `scaledCoeffMatrix`. -/
private theorem scaledCoeffRows_lower_eq_scaledCoeffMatrix_bareiss
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < i) :
    getArrayEntry (scaledCoeffRows b) i j =
      Matrix.bareiss
        (GramSchmidt.scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ hj) := by
  sorry

/-- Bareiss agrees with the Leibniz determinant on the Cramer matrix used by
the scaled-coefficient formula. -/
private theorem scaledCoeffMatrix_bareiss_eq_det
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < i) :
    ((Matrix.bareiss
        (GramSchmidt.scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ hj) :
          Int) : Rat) =
      ((Matrix.det
        (GramSchmidt.scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ hj) :
          Int) : Rat) := by
  rw [Matrix.bareiss_eq_det]

/-- The scaled-coefficient array loop writes the same diagonal determinant
values as `gramDetVecEntry`, including the zero tail after an early singular
no-pivot Bareiss step. -/
private theorem scaledCoeffRows_diag_eq_gramDetVecEntry
    (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    getArrayEntry (scaledCoeffRows b) i i =
      Int.ofNat
        (gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
          ⟨i + 1, Nat.succ_lt_succ hi⟩) := by
  sorry

/-- The scaled-coefficient loop stores the next leading Gram determinant on
the diagonal. -/
private theorem scaledCoeffRows_diag_eq_gramDet
    (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    getArrayEntry (scaledCoeffRows b) i i =
      Int.ofNat (gramDet b (i + 1) (Nat.succ_le_of_lt hi)) := by
  rw [scaledCoeffRows_diag_eq_gramDetVecEntry (b := b) i hi]
  rw [gramDetVecEntry_eq_gramDet (b := b) (i + 1) (Nat.succ_le_of_lt hi)]

theorem gramDet_zero (b : Matrix Int n m) :
    gramDet b 0 (Nat.zero_le n) = 1 := by
  rfl

theorem gramDetVec_eq_gramDet (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) :
    (gramDetVec b).get ⟨k, Nat.lt_succ_of_le hk⟩ = gramDet b k hk := by
  cases k with
  | zero =>
      rw [show hk = Nat.zero_le n from Subsingleton.elim _ _]
      rw [gramDet_zero]
      simp [gramDetVec, data, gramDetVecFromScaledCoeffRows]
  | succ r =>
      have hr : r < n := Nat.lt_of_succ_le hk
      have hdiag := scaledCoeffRows_diag_eq_gramDet (b := b) r hr
      simpa [gramDetVec, data, gramDetVecFromScaledCoeffRows] using congrArg Int.toNat hdiag

private theorem leadingGramMatrixInt_det_nonneg_pre
    (b : Matrix Int n m) (t : Nat) (ht : t ≤ n) :
    0 ≤ Matrix.det (GramSchmidt.leadingGramMatrixInt b t ht) := by
  let rowPrefix : Matrix Int t m :=
    Matrix.ofFn fun i j =>
      (b.row ⟨i.val, Nat.lt_of_lt_of_le i.isLt ht⟩)[j]
  have hgram :
      GramSchmidt.leadingGramMatrixInt b t ht =
        Matrix.gramMatrix rowPrefix := by
    apply Vector.ext
    intro i hi
    apply Vector.ext
    intro j hj
    simp [GramSchmidt.leadingGramMatrixInt, rowPrefix, Matrix.gramMatrix, Matrix.dot,
      Matrix.row, Matrix.ofFn, GramSchmidt.liftFinLE]
  rw [hgram]
  exact Matrix.det_gramMatrix_nonneg rowPrefix

private theorem gramDet_pos_of_det_positive (b : Matrix Int n m)
    (hdet : ∀ k : Fin n, 0 < Matrix.det (Matrix.submatrix (Matrix.gramMatrix b) k))
    (k : Nat) (hk : k ≤ n) (hk' : 0 < k) :
    0 < gramDet b k hk := by
  cases k with
  | zero =>
      omega
  | succ r =>
      have hrn : r < n := Nat.lt_of_succ_le hk
      let last : Fin n := ⟨r, hrn⟩
      have hsub : 0 < Matrix.det (Matrix.submatrix (Matrix.gramMatrix b) last) :=
        hdet last
      have hsub_eq :
          Matrix.submatrix (Matrix.gramMatrix b) last =
            GramSchmidt.leadingGramMatrixInt b (r + 1) hk := by
        rw [Matrix.submatrix_eq_leadingPrefix]
        rw [GramSchmidt.leadingGramMatrixInt_eq_leadingPrefix_gram]
      have hdet_pos :
          0 < Matrix.det (GramSchmidt.leadingGramMatrixInt b (r + 1) hk) := by
        simpa [hsub_eq] using hsub
      have hdet_nat :
          Matrix.det (GramSchmidt.leadingGramMatrixInt b (r + 1) hk) =
            Int.ofNat (gramDet b (r + 1) hk) := by
        rw [gramDet, Matrix.bareiss_eq_det]
        exact (Int.toNat_of_nonneg
          (leadingGramMatrixInt_det_nonneg_pre b (r + 1) hk)).symm
      have hnat_int : 0 < Int.ofNat (gramDet b (r + 1) hk) := by
        simpa [hdet_nat] using hdet_pos
      exact Int.ofNat_lt.mp hnat_int

/-- A determinant-positive leading-Gram-prefix proof induces the executable
`gramDet` independence predicate. This is useful for callers that already
have determinant lemmas for special matrix families, while keeping the public
predicate stated over Mathlib-free computed data. -/
theorem independent_of_det_positive (b : Matrix Int n m)
    (hdet : ∀ k : Fin n, 0 < Matrix.det (Matrix.submatrix (Matrix.gramMatrix b) k)) :
    independent b := by
  intro k
  exact gramDet_pos_of_det_positive b hdet (k.val + 1) (Nat.succ_le_of_lt k.isLt)
    (Nat.succ_pos k.val)

theorem independent_one {n : Nat} : independent (1 : Matrix Int n n) := by
  exact independent_of_det_positive (1 : Matrix Int n n) (by
    intro k
    rw [Matrix.gramMatrix_one, Matrix.submatrix_one, Matrix.det_one]
    decide)

private theorem gramDet_pos_core (b : Matrix Int n m)
    (hli : independent b) (k : Nat) (hk : k ≤ n) (hk' : 0 < k) :
    0 < gramDet b k hk := by
  cases k with
  | zero =>
      omega
  | succ r =>
      have hrn : r < n := Nat.lt_of_succ_le hk
      exact hli ⟨r, hrn⟩

/-! ### Helpers for `gramDet_eq_prod_normSq_core`

The remaining theorems below build the rational column-operation reduction
from the leading Gram matrix to the diagonal Gram-Schmidt norm-squared
matrix, plus the integer→rational cast bridge for `det`. -/

/-- Casting Int → Rat distributes over a `List.foldl` sum. -/
private theorem foldl_intCast_add_aux {α : Type v}
    (xs : List α) (f : α → Int) (acc : Int) :
    ((xs.foldl (fun acc x => acc + f x) acc : Int) : Rat) =
      xs.foldl (fun (acc' : Rat) x => acc' + ((f x : Int) : Rat)) ((acc : Rat)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hi := ih (acc := acc + f x)
      simpa [Rat.intCast_add] using hi

/-- Casting Int → Rat distributes over a `List.foldl` product. -/
private theorem foldl_intCast_mul_aux {α : Type v}
    (xs : List α) (f : α → Int) (acc : Int) :
    ((xs.foldl (fun acc x => acc * f x) acc : Int) : Rat) =
      xs.foldl (fun (acc' : Rat) x => acc' * ((f x : Int) : Rat)) ((acc : Rat)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hi := ih (acc := acc * f x)
      simpa [Rat.intCast_mul] using hi

/-- `detSign` produces `1` or `-1`, which lifts identically through the
Int → Rat cast. -/
private theorem detSign_intCast {k : Nat} (perm : Vector (Fin k) k) :
    ((Matrix.detSign perm : Int) : Rat) = (Matrix.detSign perm : Rat) := by
  unfold Matrix.detSign
  by_cases h : Matrix.inversionCount perm.toList % 2 = 0
  · simp [h]
  · simp [h]

/-- The cast of an Int matrix to a Rat matrix by entry-wise Int.cast. -/
private def castIntDetMatrix {k : Nat} (M : Matrix Int k k) : Matrix Rat k k :=
  Matrix.ofFn fun i j => ((M[i][j] : Int) : Rat)

@[simp] private theorem castIntDetMatrix_get {k : Nat}
    (M : Matrix Int k k) (i j : Fin k) :
    (castIntDetMatrix M)[i][j] = ((M[i][j] : Int) : Rat) := by
  simp [castIntDetMatrix, Matrix.ofFn]

private theorem foldl_mul_congr_simple {α : Type v} {R : Type w} [Mul R]
    (xs : List α) (f g : α → R) (acc : R)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.foldl (fun acc x => acc * f x) acc =
      xs.foldl (fun acc x => acc * g x) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = g x := h x (by simp)
      rw [hx]
      exact ih (acc * g x) (fun y hy => h y (by simp [hy]))

private theorem detProduct_intCast {k : Nat}
    (M : Matrix Int k k) (perm : Vector (Fin k) k) :
    ((Matrix.detProduct M perm : Int) : Rat) =
      Matrix.detProduct (castIntDetMatrix M) perm := by
  unfold Matrix.detProduct
  rw [foldl_intCast_mul_aux (xs := List.finRange k)
    (f := fun i => M[i][perm[i]]) (acc := 1)]
  rw [show ((1 : Int) : Rat) = (1 : Rat) from rfl]
  apply foldl_mul_congr_simple
  intro i _hi
  rw [castIntDetMatrix_get]

private theorem detTerm_intCast {k : Nat}
    (M : Matrix Int k k) (perm : Vector (Fin k) k) :
    ((Matrix.detTerm M perm : Int) : Rat) =
      Matrix.detTerm (castIntDetMatrix M) perm := by
  unfold Matrix.detTerm
  rw [Rat.intCast_mul, detSign_intCast, detProduct_intCast]

private theorem foldl_sum_congr_simple {α : Type v} {R : Type w} [Add R]
    (xs : List α) (f g : α → R) (acc : R)
    (h : ∀ x ∈ xs, f x = g x) :
    xs.foldl (fun acc x => acc + f x) acc =
      xs.foldl (fun acc x => acc + g x) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons]
      have hx : f x = g x := h x (by simp)
      rw [hx]
      exact ih (acc + g x) (fun y hy => h y (by simp [hy]))

private theorem det_intCast {k : Nat} (M : Matrix Int k k) :
    ((Matrix.det M : Int) : Rat) = Matrix.det (castIntDetMatrix M) := by
  unfold Matrix.det
  rw [foldl_intCast_add_aux (xs := Matrix.permutationVectors k)
    (f := fun perm => Matrix.detTerm M perm) (acc := 0)]
  rw [show ((0 : Int) : Rat) = (0 : Rat) from rfl]
  apply foldl_sum_congr_simple
  intro perm _hperm
  exact detTerm_intCast M perm

/-- Right-side dot product distributes over vector addition. -/
private theorem dot_add_right_rat {m' : Nat} (u v w : Vector Rat m') :
    Matrix.dot u (v + w) = Matrix.dot u v + Matrix.dot u w := by
  unfold Matrix.dot Hex.Vector.dotProduct
  have h :
      ∀ (xs : List (Fin m')) (accV accW : Rat),
        xs.foldl (fun acc i => acc + u[i] * (v + w)[i]) (accV + accW) =
          xs.foldl (fun acc i => acc + u[i] * v[i]) accV +
            xs.foldl (fun acc i => acc + u[i] * w[i]) accW := by
    intro xs
    induction xs with
    | nil => intro accV accW; simp
    | cons i xs ih =>
        intro accV accW
        have hentry : (v + w)[i] = v[i] + w[i] := by
          change (v + w)[i.val] = v[i.val] + w[i.val]
          rw [Vector.getElem_add]
        simp only [List.foldl_cons]
        have hstart :
            accV + accW + u[i] * (v + w)[i] =
              (accV + u[i] * v[i]) + (accW + u[i] * w[i]) := by
          rw [hentry]
          grind
        rw [hstart]
        exact ih (accV + u[i] * v[i]) (accW + u[i] * w[i])
  have hzero : (0 : Rat) + 0 = 0 := by grind
  simpa [hzero] using h (List.finRange m') 0 0

/-- Right-side dot product distributes over scalar multiplication. -/
private theorem dot_smul_right_rat {m' : Nat} (s : Rat) (u v : Vector Rat m') :
    Matrix.dot u (s • v) = s * Matrix.dot u v := by
  unfold Matrix.dot Hex.Vector.dotProduct
  have h :
      ∀ (xs : List (Fin m')) (acc : Rat),
        xs.foldl (fun acc i => acc + u[i] * (s • v)[i]) (s * acc) =
          s * xs.foldl (fun acc i => acc + u[i] * v[i]) acc := by
    intro xs
    induction xs with
    | nil => intro acc; simp
    | cons i xs ih =>
        intro acc
        have hentry : (s • v)[i] = s * v[i] := by
          change (s • v)[i.val] = s * v[i.val]
          rw [Vector.getElem_smul]
          rfl
        simp only [List.foldl_cons]
        have hstart :
            s * acc + u[i] * (s • v)[i] = s * (acc + u[i] * v[i]) := by
          rw [hentry]
          grind
        rw [hstart]
        exact ih (acc + u[i] * v[i])
  have hzero : s * (0 : Rat) = 0 := by grind
  simpa [hzero] using h (List.finRange m') 0

/-- Dot product of a vector against the zero vector is zero. -/
private theorem dot_zero_right_rat {m' : Nat} (u : Vector Rat m') :
    Matrix.dot u (0 : Vector Rat m') = 0 := by
  unfold Matrix.dot Hex.Vector.dotProduct
  have h : ∀ (xs : List (Fin m')) (acc : Rat),
      xs.foldl (fun acc i => acc + u[i] * (0 : Vector Rat m')[i]) acc = acc := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons i xs ih =>
        intro acc
        simp only [List.foldl_cons]
        have hzero : (0 : Vector Rat m')[i] = 0 := by
          change (0 : Vector Rat m')[i.val] = 0
          rw [Vector.getElem_zero]
        rw [hzero]
        have : acc + u[i] * 0 = acc := by grind
        rw [this]
        exact ih acc
  exact h (List.finRange m') 0

/-- Folding a sum with an initial value separates: the result equals the
initial value plus the same fold from zero. -/
private theorem foldl_sum_start_rat {α : Type v}
    (xs : List α) (f : α → Rat) (acc : Rat) :
    xs.foldl (fun acc x => acc + f x) acc =
      acc + xs.foldl (fun acc x => acc + f x) 0 := by
  induction xs generalizing acc with
  | nil => simp; grind
  | cons x xs ih =>
      simp only [List.foldl_cons]
      rw [ih (acc := acc + f x)]
      rw [ih (acc := (0 : Rat) + f x)]
      grind

/-- Rational dot product is commutative. -/
private theorem dot_comm_rat {m' : Nat} (u v : Vector Rat m') :
    Matrix.dot u v = Matrix.dot v u := by
  unfold Matrix.dot Hex.Vector.dotProduct
  have h : ∀ (xs : List (Fin m')) (accU accV : Rat),
      accU = accV →
        xs.foldl (fun acc i => acc + u[i] * v[i]) accU =
          xs.foldl (fun acc i => acc + v[i] * u[i]) accV := by
    intro xs
    induction xs with
    | nil => intro accU accV h; exact h
    | cons i xs ih =>
        intro accU accV h
        simp only [List.foldl_cons]
        apply ih
        rw [h]
        grind
  exact h (List.finRange m') 0 0 rfl

/-- Right-side dot product distribution over a `prefixCombination`. -/
private theorem dot_prefixCombination_right_rat
    (coeffs : Matrix Rat n n) (basisM : Matrix Rat n m)
    (i : Nat) (hi : i < n) (u : Vector Rat m) :
    Matrix.dot u (GramSchmidt.prefixCombination coeffs basisM i hi) =
      (List.finRange i).foldl
        (fun (acc : Rat) (j : Fin i) =>
          acc +
            GramSchmidt.entry coeffs ⟨i, hi⟩
                ⟨j.val, Nat.lt_trans j.isLt hi⟩ *
              Matrix.dot u
                (basisM.row ⟨j.val, Nat.lt_trans j.isLt hi⟩)) 0 := by
  unfold GramSchmidt.prefixCombination
  have hgen :
      ∀ (xs : List (Fin i)) (acc : Vector Rat m),
        Matrix.dot u
            (xs.foldl
              (fun acc (j : Fin i) =>
                acc +
                  GramSchmidt.entry coeffs ⟨i, hi⟩
                      ⟨j.val, Nat.lt_trans j.isLt hi⟩ •
                    basisM.row ⟨j.val, Nat.lt_trans j.isLt hi⟩)
              acc) =
          Matrix.dot u acc +
            xs.foldl
              (fun (acc' : Rat) (j : Fin i) =>
                acc' +
                  GramSchmidt.entry coeffs ⟨i, hi⟩
                      ⟨j.val, Nat.lt_trans j.isLt hi⟩ *
                    Matrix.dot u
                      (basisM.row ⟨j.val, Nat.lt_trans j.isLt hi⟩)) 0 := by
    intro xs
    induction xs with
    | nil =>
        intro acc
        simp; grind
    | cons x xs ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [ih]
        rw [dot_add_right_rat, dot_smul_right_rat]
        rw [foldl_sum_start_rat xs _
          ((0 : Rat) + (GramSchmidt.entry coeffs ⟨i, hi⟩
              ⟨x.val, Nat.lt_trans x.isLt hi⟩ *
            Matrix.dot u
              (basisM.row ⟨x.val, Nat.lt_trans x.isLt hi⟩)))]
        grind
  rw [hgen (List.finRange i) 0]
  rw [dot_zero_right_rat]
  grind

/-- Dot product against a `prefixCombination` is zero when the right vector is
orthogonal to every contributing basis row. -/
private theorem dot_prefixCombination_right_eq_zero_of_dot_zero
    (coeffs : Matrix Rat n n) (basisM : Matrix Rat n m)
    (i : Nat) (hi : i < n) (u : Vector Rat m)
    (h : ∀ (j : Fin i),
      Matrix.dot u
          (basisM.row ⟨j.val, Nat.lt_trans j.isLt hi⟩) = 0) :
    Matrix.dot u (GramSchmidt.prefixCombination coeffs basisM i hi) = 0 := by
  rw [dot_prefixCombination_right_rat]
  -- All terms are zero: the foldl with each entry = 0 reduces to 0.
  induction (List.finRange i) with
  | nil => rfl
  | cons j xs ih =>
      simp only [List.foldl_cons]
      rw [h j]
      have h0 : (0 : Rat) + GramSchmidt.entry coeffs ⟨i, hi⟩
          ⟨j.val, Nat.lt_trans j.isLt hi⟩ * 0 = 0 := by grind
      rw [h0]
      exact ih

/-- Cast an Int matrix row to a Rat row by entry-wise `Int.cast`. -/
private def castIntRow (b : Matrix Int n m) (i : Fin n) : Vector Rat m :=
  Vector.map (fun x : Int => (x : Rat)) (b.row i)

/-- Cast an Int matrix to the Rat matrix whose rows are `castIntRow`. -/
private def castIntMatrixRat (b : Matrix Int n m) : Matrix Rat n m :=
  Vector.map (fun row => Vector.map (fun x : Int => (x : Rat)) row) b

/-- Coefficients of the projection of row `i` onto the Gram-Schmidt prefix
`0, ..., j`, indexed by that prefix. -/
private noncomputable def projectionCoeffPrefix
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < n) :
    Vector Rat (j + 1) :=
  Vector.ofFn fun q =>
    GramSchmidt.entry (coeffs b) ⟨i, hi⟩
      ⟨q.val, Nat.lt_of_lt_of_le q.isLt (Nat.succ_le_of_lt hj)⟩

/-- The Gram-Schmidt prefix projection of row `i` onto rows `0, ..., j`, still
written in the orthogonal basis rows. -/
private noncomputable def basisPrefixProjection
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < n) :
    Vector Rat m :=
  Matrix.rowCombination (GramSchmidt.prefixRows (basis b) j hj)
    (projectionCoeffPrefix b i j hi hj)

private theorem basisPrefixProjection_mem_basisSpan
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < n) :
    GramSchmidt.prefixSpan (basis b) j hj
      (basisPrefixProjection b i j hi hj) := by
  exact ⟨projectionCoeffPrefix b i j hi hj, rfl⟩

private theorem basisPrefixProjection_mem_originalSpan
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < n) :
    GramSchmidt.prefixSpan (castIntMatrixRat b) j hj
      (basisPrefixProjection b i j hi hj) := by
  simpa [castIntMatrixRat] using
    ((basis_span b j hj (basisPrefixProjection b i j hi hj)).mp
      (basisPrefixProjection_mem_basisSpan b i j hi hj))

/-- Original-row coordinates for the projection of row `i` onto the row prefix
`0, ..., j`. The coordinates are chosen through the proved span equivalence
between original rows and Gram-Schmidt rows. -/
private noncomputable def originalProjectionCoords
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < n) :
    Vector Rat (j + 1) :=
  Classical.choose (basisPrefixProjection_mem_originalSpan b i j hi hj)

/-- The chosen original-row coordinates reconstruct the same projection vector
as the Gram-Schmidt prefix coefficients. -/
private theorem originalProjectionCoords_spec
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < n) :
    Matrix.rowCombination (GramSchmidt.prefixRows (castIntMatrixRat b) j hj)
        (originalProjectionCoords b i j hi hj) =
      basisPrefixProjection b i j hi hj := by
  exact Classical.choose_spec (basisPrefixProjection_mem_originalSpan b i j hi hj)

private theorem rowCombination_eq_foldl_rows_rat
    (M : Matrix Rat n m) (c : Vector Rat n) :
    Matrix.rowCombination M c =
      (List.finRange n).foldl (fun acc j => acc + c[j] • M.row j) 0 := by
  apply Vector.ext
  intro idx hidx
  let idxFin : Fin m := ⟨idx, hidx⟩
  change (Matrix.mulVec (Matrix.transpose M) c)[idxFin] =
    ((List.finRange n).foldl (fun acc j => acc + c[j] • M.row j) 0)[idxFin]
  rw [show
      (Matrix.mulVec (Matrix.transpose M) c)[idxFin] =
        (List.finRange n).foldl
          (fun acc j => acc + M[j.val][idxFin.val] * c[j])
          0 by
        unfold Matrix.mulVec Matrix.transpose Matrix.col Matrix.row Matrix.dot
          Hex.Vector.dotProduct
        simp]
  have hfold :
      ∀ xs : List (Fin n), ∀ accL : Rat, ∀ accR : Vector Rat m,
        accL = accR[idxFin] →
        xs.foldl (fun acc j => acc + M[j.val][idxFin.val] * c[j]) accL =
          (xs.foldl (fun acc j => acc + c[j] • M.row j) accR)[idxFin] := by
    intro xs
    induction xs with
    | nil =>
        intro accL accR hacc
        simp [hacc]
    | cons j rest ih =>
        intro accL accR hacc
        simp only [List.foldl_cons]
        apply ih
        change accL + M[j.val][idxFin.val] * c[j] =
          (accR + c[j] • M.row j)[idxFin.val]
        rw [Vector.getElem_add, Vector.getElem_smul]
        rw [hacc]
        change accR[idx] + M[j.val][idx] * c[j] =
          accR[idx] + c[j] * M[j.val][idx]
        grind
  exact hfold (List.finRange n) 0 0 (by simp [Vector.getElem_zero])

private theorem dot_rowCombination_right_rat
    (u : Vector Rat m) (M : Matrix Rat n m) (c : Vector Rat n) :
    Matrix.dot u (Matrix.rowCombination M c) =
      (List.finRange n).foldl
        (fun acc j => acc + c[j] * Matrix.dot u (M.row j)) 0 := by
  rw [rowCombination_eq_foldl_rows_rat]
  have hgen :
      ∀ xs : List (Fin n), ∀ acc : Vector Rat m,
        Matrix.dot u (xs.foldl (fun acc j => acc + c[j] • M.row j) acc) =
          Matrix.dot u acc +
            xs.foldl (fun acc' j => acc' + c[j] * Matrix.dot u (M.row j)) 0 := by
    intro xs
    induction xs with
    | nil =>
        intro acc
        simp only [List.foldl_nil]
        grind
    | cons x xs ih =>
        intro acc
        simp only [List.foldl_cons]
        rw [ih]
        rw [dot_add_right_rat, dot_smul_right_rat]
        rw [foldl_sum_start_rat xs _
          ((0 : Rat) + c[x] * Matrix.dot u (M.row x))]
        grind
  rw [hgen (List.finRange n) 0]
  rw [dot_zero_right_rat]
  grind

/-- Dotting the projection with an original prefix row is the corresponding
linear combination of original Gram-matrix entries. -/
private theorem originalProjectionCoords_dot_eq_gram_combination
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < n)
    (p : Fin (j + 1)) :
    Matrix.dot
        (castIntRow b
          ⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.succ_le_of_lt hj)⟩)
        (basisPrefixProjection b i j hi hj) =
      (List.finRange (j + 1)).foldl
        (fun acc q =>
          acc + (originalProjectionCoords b i j hi hj)[q] *
            Matrix.dot
              (castIntRow b
                ⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.succ_le_of_lt hj)⟩)
              (castIntRow b
                ⟨q.val, Nat.lt_of_lt_of_le q.isLt (Nat.succ_le_of_lt hj)⟩)) 0 := by
  rw [← originalProjectionCoords_spec b i j hi hj]
  rw [dot_rowCombination_right_rat]
  apply foldl_sum_congr_simple
  intro q _hq
  simp [GramSchmidt.prefixRows, Matrix.row, castIntMatrixRat, castIntRow]

/-- Auxiliary matrix `M_final` whose `(i, j)` entry is the rational inner
product `⟨b_i, b*_j⟩` between the cast integer row `b_i` and the
Gram-Schmidt orthogonal basis row `b*_j`. -/
private noncomputable def auxMatrix (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) :
    Matrix Rat k k :=
  Matrix.ofFn fun i j =>
    Matrix.dot (castIntRow b (GramSchmidt.liftFinLE i hk))
      ((basis b).row (GramSchmidt.liftFinLE j hk))

private theorem auxMatrix_get (b : Matrix Int n m) (k : Nat) (hk : k ≤ n)
    (i j : Fin k) :
    (auxMatrix b k hk)[i][j] =
      Matrix.dot (castIntRow b (GramSchmidt.liftFinLE i hk))
        ((basis b).row (GramSchmidt.liftFinLE j hk)) := by
  simp [auxMatrix, Matrix.ofFn]

/-- The cast Int row decomposes as `b*_i + prefixCombination`. -/
private theorem castIntRow_decomposition
    (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    castIntRow b ⟨i, hi⟩ =
      (basis b).row ⟨i, hi⟩ +
        GramSchmidt.prefixCombination (coeffs b) (basis b) i hi := by
  exact basis_decomposition (b := b) i hi

/-- `auxMatrix` is lower triangular: entries above the diagonal vanish. -/
private theorem auxMatrix_zero_above (b : Matrix Int n m) (k : Nat) (hk : k ≤ n)
    (i j : Fin k) (hij : i.val < j.val) :
    (auxMatrix b k hk)[i][j] = 0 := by
  rw [auxMatrix_get]
  have hi' : i.val < n := Nat.lt_of_lt_of_le i.isLt hk
  have hj' : j.val < n := Nat.lt_of_lt_of_le j.isLt hk
  have hij' : i.val ≠ j.val := Nat.ne_of_lt hij
  -- liftFinLE i hk = ⟨i.val, hi'⟩ definitionally.
  rw [show GramSchmidt.liftFinLE i hk = ⟨i.val, hi'⟩ from rfl]
  rw [show GramSchmidt.liftFinLE j hk = ⟨j.val, hj'⟩ from rfl]
  rw [castIntRow_decomposition b i.val hi']
  rw [dot_comm_rat]
  rw [dot_add_right_rat]
  rw [dot_comm_rat ((basis b).row ⟨j.val, hj'⟩) ((basis b).row ⟨i.val, hi'⟩)]
  rw [basis_orthogonal b i.val j.val hi' hj' hij']
  -- Second term: prefixCombination orthogonal to ((basis b).row j).
  have hprefix :
      Matrix.dot ((basis b).row ⟨j.val, hj'⟩)
          (GramSchmidt.prefixCombination (coeffs b) (basis b) i.val hi') = 0 := by
    apply dot_prefixCombination_right_eq_zero_of_dot_zero
      (coeffs := coeffs b) (basisM := basis b) (i := i.val) (hi := hi')
      (u := (basis b).row ⟨j.val, hj'⟩)
    intro p
    have hp' : p.val < i.val := p.isLt
    have hpj : p.val ≠ j.val := Nat.ne_of_lt (Nat.lt_trans hp' hij)
    have hpj_lt : p.val < n := Nat.lt_trans hp' hi'
    exact basis_orthogonal b j.val p.val hj' hpj_lt fun h => hpj h.symm
  rw [hprefix]
  grind

/-- Diagonal of `auxMatrix` is the squared norm of the corresponding basis row. -/
private theorem auxMatrix_diag (b : Matrix Int n m) (k : Nat) (hk : k ≤ n)
    (i : Fin k) :
    (auxMatrix b k hk)[i][i] =
      Vector.normSq ((basis b).row (GramSchmidt.liftFinLE i hk)) := by
  rw [auxMatrix_get]
  have hi' : i.val < n := Nat.lt_of_lt_of_le i.isLt hk
  rw [show GramSchmidt.liftFinLE i hk = ⟨i.val, hi'⟩ from rfl]
  rw [castIntRow_decomposition b i.val hi']
  rw [dot_comm_rat]
  rw [dot_add_right_rat]
  -- First term: dot ((basis b).row i) ((basis b).row i) = normSq ((basis b).row i)
  -- Second term: dot ((basis b).row i) prefixCombination = 0.
  have hprefix :
      Matrix.dot ((basis b).row ⟨i.val, hi'⟩)
          (GramSchmidt.prefixCombination (coeffs b) (basis b) i.val hi') = 0 := by
    apply dot_prefixCombination_right_eq_zero_of_dot_zero
      (coeffs := coeffs b) (basisM := basis b) (i := i.val) (hi := hi')
      (u := (basis b).row ⟨i.val, hi'⟩)
    intro p
    have hp' : p.val < i.val := p.isLt
    have hpi : p.val ≠ i.val := Nat.ne_of_lt hp'
    have hpi_lt : p.val < n := Nat.lt_trans hp' hi'
    exact basis_orthogonal b i.val p.val hi' hpi_lt fun h => hpi h.symm
  rw [hprefix]
  -- Remaining: dot ((basis b).row i) ((basis b).row i) + 0 = normSq ((basis b).row i)
  have hns :
      Vector.normSq ((basis b).row ⟨i.val, hi'⟩) =
        Matrix.dot ((basis b).row ⟨i.val, hi'⟩) ((basis b).row ⟨i.val, hi'⟩) := by
    rfl
  rw [hns]
  grind

/-- The determinant of `auxMatrix` equals the product of squared norms. -/
private theorem auxMatrix_det_eq_prod_normSq (b : Matrix Int n m)
    (k : Nat) (hk : k ≤ n) :
    Matrix.det (auxMatrix b k hk) = gramSchmidtNormProduct b k hk := by
  rw [Matrix.det_lowerTriangular_eq_foldl_diag (auxMatrix b k hk)
    (fun i j hij => auxMatrix_zero_above b k hk i j hij)]
  unfold gramSchmidtNormProduct
  -- Both foldls are over `List.finRange k`. The diagonal of auxMatrix at i
  -- equals Vector.normSq of (basis b) row at the lifted index.
  apply foldl_mul_congr_simple
  intro i _hi
  rw [auxMatrix_diag b k hk i]
  rfl

/-- Interpolating matrix between `leadingGramMatrixRat (castIntMatrix b)` (at
`s = 0`) and `auxMatrix b k hk` (at `s = k`). Columns with index `< s` have
already been replaced by basis-row dot products; columns with index `≥ s`
still hold the original `b`-row dot products. -/
private noncomputable def progressMatrix (b : Matrix Int n m) (k : Nat)
    (hk : k ≤ n) (s : Nat) : Matrix Rat k k :=
  Matrix.ofFn fun i j =>
    if j.val < s then
      Matrix.dot (castIntRow b (GramSchmidt.liftFinLE i hk))
        ((basis b).row (GramSchmidt.liftFinLE j hk))
    else
      Matrix.dot (castIntRow b (GramSchmidt.liftFinLE i hk))
        (castIntRow b (GramSchmidt.liftFinLE j hk))

private theorem progressMatrix_get_lt (b : Matrix Int n m) (k : Nat) (hk : k ≤ n)
    (s : Nat) (i j : Fin k) (hj : j.val < s) :
    (progressMatrix b k hk s)[i][j] =
      Matrix.dot (castIntRow b (GramSchmidt.liftFinLE i hk))
        ((basis b).row (GramSchmidt.liftFinLE j hk)) := by
  simp [progressMatrix, Matrix.ofFn, hj]

private theorem progressMatrix_get_ge (b : Matrix Int n m) (k : Nat) (hk : k ≤ n)
    (s : Nat) (i j : Fin k) (hj : ¬ j.val < s) :
    (progressMatrix b k hk s)[i][j] =
      Matrix.dot (castIntRow b (GramSchmidt.liftFinLE i hk))
        (castIntRow b (GramSchmidt.liftFinLE j hk)) := by
  simp [progressMatrix, Matrix.ofFn, hj]

/-- At `s = k`, `progressMatrix` matches `auxMatrix`. -/
private theorem progressMatrix_full_eq_auxMatrix (b : Matrix Int n m)
    (k : Nat) (hk : k ≤ n) :
    progressMatrix b k hk k = auxMatrix b k hk := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let ii : Fin k := ⟨i, hi⟩
  let jj : Fin k := ⟨j, hj⟩
  have hjlt : jj.val < k := hj
  change (progressMatrix b k hk k)[ii][jj] = (auxMatrix b k hk)[ii][jj]
  rw [progressMatrix_get_lt b k hk k ii jj hjlt]
  rw [auxMatrix_get]

/-- The col-op coefficient list for the `s`-th transition step: indices
`p : Fin s` lifted into `Fin k`. -/
private def progressMatrixSources (k : Nat) (s : Nat) (hs : s < k) :
    List (Fin k) :=
  (List.finRange s).map fun p => ⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.le_of_lt hs)⟩

/-- Sources are all strictly below `s` and hence distinct from `⟨s, hs⟩`. -/
private theorem progressMatrixSources_ne_dst (k : Nat) (s : Nat) (hs : s < k)
    (src : Fin k) (hmem : src ∈ progressMatrixSources k s hs) :
    src ≠ ⟨s, hs⟩ := by
  unfold progressMatrixSources at hmem
  rw [List.mem_map] at hmem
  obtain ⟨p, _, hp⟩ := hmem
  intro h
  have hval := congrArg Fin.val h
  rw [← hp] at hval
  exact Nat.ne_of_lt p.isLt hval

/-- The col-op coefficient for source `src : Fin k`: equals
`-(coeffs b)[s][src.val]`. -/
private noncomputable def progressMatrixCoeff (b : Matrix Int n m) (k : Nat)
    (hk : k ≤ n) (s : Nat) (hs : s < k) (src : Fin k) : Rat :=
  -(GramSchmidt.entry (coeffs b)
    ⟨s, Nat.lt_of_lt_of_le hs hk⟩
    ⟨src.val, Nat.lt_of_lt_of_le src.isLt hk⟩)

/-- The matrix transition for one col-op step: column `s` of
`progressMatrix b k hk (s+1)` equals column `s` of `progressMatrix b k hk s`
plus a linear combination of columns with index `< s`. -/
private theorem progressMatrix_succ_eq_colReplace
    (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) (s : Nat) (hs : s < k) :
    progressMatrix b k hk (s + 1) =
      Matrix.colReplace (progressMatrix b k hk s) (⟨s, hs⟩ : Fin k)
        (fun i =>
          (progressMatrix b k hk s)[i][(⟨s, hs⟩ : Fin k)] +
          (progressMatrixSources k s hs).foldl
            (fun acc src =>
              acc + progressMatrixCoeff b k hk s hs src *
                (progressMatrix b k hk s)[i][src]) 0) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let ii : Fin k := ⟨i, hi⟩
  change (progressMatrix b k hk (s + 1))[ii][(⟨j, hj⟩ : Fin k)] =
    (Matrix.colReplace (progressMatrix b k hk s) (⟨s, hs⟩ : Fin k)
      (fun i' =>
        (progressMatrix b k hk s)[i'][(⟨s, hs⟩ : Fin k)] +
        (progressMatrixSources k s hs).foldl
          (fun acc src =>
            acc + progressMatrixCoeff b k hk s hs src *
              (progressMatrix b k hk s)[i'][src]) 0))[ii][(⟨j, hj⟩ : Fin k)]
  rw [Matrix.colReplace_get]
  -- Case split on Fin k equality.
  by_cases hjs : (⟨j, hj⟩ : Fin k) = (⟨s, hs⟩ : Fin k)
  · -- Column s case.
    rw [if_pos hjs]
    -- Get j = s from the Fin equality, then substitute hj with hs.
    have hjs_val : j = s := congrArg Fin.val hjs
    -- Replace [⟨j, hj⟩] with [⟨s, hs⟩] in the LHS by the Fin equality.
    -- Use Vector.ext-like rewrite: re-express the LHS at ⟨s, hs⟩ via congrArg.
    have hLHS_eq :
        (progressMatrix b k hk (s + 1))[ii][(⟨j, hj⟩ : Fin k)] =
          (progressMatrix b k hk (s + 1))[ii][(⟨s, hs⟩ : Fin k)] := by
      congr 1
    rw [hLHS_eq]
    -- LHS: progressMatrix b k hk (s+1) at column ⟨s, hs⟩.
    have hjlt : (⟨s, hs⟩ : Fin k).val < s + 1 := Nat.lt_succ_self s
    rw [progressMatrix_get_lt b k hk (s + 1) ii (⟨s, hs⟩ : Fin k) hjlt]
    have hjnlt : ¬ (⟨s, hs⟩ : Fin k).val < s := Nat.lt_irrefl s
    rw [progressMatrix_get_ge b k hk s ii (⟨s, hs⟩ : Fin k) hjnlt]
    -- LHS = Matrix.dot (castIntRow b (lift ii)) ((basis b).row (lift ⟨s, hs⟩))
    -- RHS' first piece = Matrix.dot (castIntRow b (lift ii)) (castIntRow b (lift ⟨s, hs⟩))
    -- We need: LHS = RHS' first + foldl (coeff * (basis row p))
    have hsn : s < n := Nat.lt_of_lt_of_le hs hk
    have hslift : GramSchmidt.liftFinLE (⟨s, hs⟩ : Fin k) hk = ⟨s, hsn⟩ := rfl
    rw [hslift]
    -- decomposition castIntRow b ⟨s, hsn⟩ = (basis b).row ⟨s, hsn⟩ + prefixComb
    rw [castIntRow_decomposition b s hsn]
    rw [dot_add_right_rat]
    -- LHS = dot (castIntRow ii) ((basis b).row ⟨s, _⟩)
    -- RHS_first = dot (castIntRow ii) ((basis b).row ⟨s, _⟩) + dot (castIntRow ii) prefixComb
    -- So we need: dot (castIntRow ii) ((basis b).row ⟨s,_⟩) = (above) + foldl
    -- => 0 = dot (castIntRow ii) prefixComb + foldl
    -- Use: dot (castIntRow ii) prefixComb = foldl coeff * dot (castIntRow ii) basis_row_p
    -- And dot (castIntRow ii) basis_row_p = progressMatrix s at [ii][⟨p, _⟩] for p < s.
    rw [dot_prefixCombination_right_rat (coeffs := coeffs b) (basisM := basis b)
      (i := s) (hi := hsn)]
    -- Now show the two foldls cancel.
    -- The foldl on the LHS has +entry * dot, and we need to match the - on RHS.
    -- It's easier to subtract from both sides to show RHS - LHS = 0.
    -- Actually: LHS + foldl_lhs = LHS_first + foldl_rhs
    -- where foldl_lhs has positive entries, foldl_rhs has negative entries.
    -- Equivalently: foldl_lhs + foldl_rhs = 0 (since LHS = LHS_first).
    -- Let's match them.
    have hfold_match :
        (List.finRange s).foldl
          (fun (acc : Rat) (jp : Fin s) =>
            acc +
              GramSchmidt.entry (coeffs b) ⟨s, hsn⟩
                  ⟨jp.val, Nat.lt_trans jp.isLt hsn⟩ *
                Matrix.dot (castIntRow b (GramSchmidt.liftFinLE ii hk))
                  ((basis b).row ⟨jp.val, Nat.lt_trans jp.isLt hsn⟩)) 0 =
        - ((progressMatrixSources k s hs).foldl
          (fun acc src =>
            acc + progressMatrixCoeff b k hk s hs src *
              (progressMatrix b k hk s)[ii][src]) 0) := by
      -- Match term by term: each entry on LHS = -coeff * progressMatrix entry.
      -- The progressMatrix entry at src (which is some ⟨p.val, _⟩ for p < s)
      -- equals dot (castIntRow ii) ((basis b).row ⟨src.val, _⟩) since src.val < s.
      unfold progressMatrixSources progressMatrixCoeff
      -- Move the negation inside the foldl.
      have hneg_foldl :
          - ((List.finRange s).map fun p =>
              (⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.le_of_lt hs)⟩ : Fin k)).foldl
            (fun acc src =>
              acc + (-GramSchmidt.entry (coeffs b) ⟨s, Nat.lt_of_lt_of_le hs hk⟩
                ⟨src.val, Nat.lt_of_lt_of_le src.isLt hk⟩) *
                (progressMatrix b k hk s)[ii][src]) 0 =
            ((List.finRange s).map fun p =>
              (⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.le_of_lt hs)⟩ : Fin k)).foldl
            (fun acc src =>
              acc + GramSchmidt.entry (coeffs b) ⟨s, Nat.lt_of_lt_of_le hs hk⟩
                ⟨src.val, Nat.lt_of_lt_of_le src.isLt hk⟩ *
                (progressMatrix b k hk s)[ii][src]) 0 := by
        -- Induction over the mapped list, factoring out negation.
        generalize hmap : (List.finRange s).map (fun p : Fin s =>
              (⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.le_of_lt hs)⟩ : Fin k)) = lst
        clear hmap
        induction lst with
        | nil => simp
        | cons x xs ih =>
            simp only [List.foldl_cons]
            -- Use foldl_sum_start_rat to factor out, then match.
            rw [foldl_sum_start_rat xs _
              ((0 : Rat) + (-GramSchmidt.entry (coeffs b) ⟨s, Nat.lt_of_lt_of_le hs hk⟩
                ⟨x.val, Nat.lt_of_lt_of_le x.isLt hk⟩) *
                (progressMatrix b k hk s)[ii][x])]
            rw [foldl_sum_start_rat xs _
              ((0 : Rat) + GramSchmidt.entry (coeffs b) ⟨s, Nat.lt_of_lt_of_le hs hk⟩
                ⟨x.val, Nat.lt_of_lt_of_le x.isLt hk⟩ *
                (progressMatrix b k hk s)[ii][x])]
            grind
      rw [hneg_foldl]
      -- Now compare the LHS foldl with the foldl over the mapped list.
      -- LHS uses xs := List.finRange s indexed by p : Fin s.
      -- RHS uses xs.map (lift p), then progressMatrix at lifted src.
      -- We use List.foldl_map.
      rw [List.foldl_map]
      -- Now both foldls are over List.finRange s.
      apply foldl_sum_congr_simple
      intro p _hp
      -- LHS body: entry * dot (castIntRow ii) ((basis b).row ⟨p.val, _⟩)
      -- RHS body: entry * (progressMatrix b k hk s)[ii][⟨p.val, _⟩]
      -- Need: dot (castIntRow ii) ((basis b).row ⟨p.val, _⟩) =
      --       (progressMatrix b k hk s)[ii][⟨p.val, _⟩]
      have hp_lt : p.val < s := p.isLt
      let pp : Fin k := ⟨p.val, Nat.lt_of_lt_of_le p.isLt (Nat.le_of_lt hs)⟩
      have hpp_lt_s : pp.val < s := hp_lt
      rw [progressMatrix_get_lt b k hk s ii pp hpp_lt_s]
      rfl
    -- Now use hfold_match to conclude.
    grind
  · -- j ≠ s case.
    rw [if_neg hjs]
    have hjs_ne : j ≠ s := fun h => hjs (Fin.ext h)
    by_cases hjlt : j < s
    · -- j < s: both versions use basis-row dot.
      have hjlt' : j < s + 1 := Nat.lt_succ_of_lt hjlt
      have hj_idx_lt_succ : (⟨j, hj⟩ : Fin k).val < s + 1 := hjlt'
      have hj_idx_lt : (⟨j, hj⟩ : Fin k).val < s := hjlt
      rw [progressMatrix_get_lt b k hk (s + 1) ii (⟨j, hj⟩ : Fin k) hj_idx_lt_succ]
      rw [progressMatrix_get_lt b k hk s ii (⟨j, hj⟩ : Fin k) hj_idx_lt]
    · -- j ≥ s. Since j ≠ s, we have j > s.
      have hjge : j ≥ s := Nat.le_of_not_lt hjlt
      have hjgt : j > s := Nat.lt_of_le_of_ne hjge fun h => hjs_ne h.symm
      have hj_idx_nlt_succ : ¬ (⟨j, hj⟩ : Fin k).val < s + 1 := by
        change ¬ j < s + 1; omega
      have hj_idx_nlt : ¬ (⟨j, hj⟩ : Fin k).val < s := hjlt
      rw [progressMatrix_get_ge b k hk (s + 1) ii (⟨j, hj⟩ : Fin k) hj_idx_nlt_succ]
      rw [progressMatrix_get_ge b k hk s ii (⟨j, hj⟩ : Fin k) hj_idx_nlt]

/-- The col-op step preserves the determinant. -/
private theorem progressMatrix_succ_det
    (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) (s : Nat) (hs : s < k) :
    Matrix.det (progressMatrix b k hk (s + 1)) =
      Matrix.det (progressMatrix b k hk s) := by
  rw [progressMatrix_succ_eq_colReplace b k hk s hs]
  apply Matrix.det_colReplace_add_otherCols
  exact progressMatrixSources_ne_dst k s hs

/-- All progress matrices have the same determinant: induct from 0 to k. -/
private theorem progressMatrix_det_invariant
    (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) (s : Nat) (hs : s ≤ k) :
    Matrix.det (progressMatrix b k hk s) = Matrix.det (progressMatrix b k hk 0) := by
  induction s with
  | zero => rfl
  | succ s ih =>
      have hslt : s < k := Nat.lt_of_succ_le hs
      have hsle : s ≤ k := Nat.le_of_lt hslt
      rw [progressMatrix_succ_det b k hk s hslt]
      exact ih hsle

/-- Dot product of cast integer rows equals the rational cast of the integer
dot product. -/
private theorem dot_castIntRow_eq_cast_dot
    (b : Matrix Int n m) (i j : Fin n) :
    Matrix.dot (castIntRow b i) (castIntRow b j) =
      ((Matrix.dot (b.row i) (b.row j) : Int) : Rat) := by
  unfold Matrix.dot Hex.Vector.dotProduct
  rw [foldl_intCast_add_aux (xs := List.finRange m)
    (f := fun k : Fin m => (b.row i)[k] * (b.row j)[k]) (acc := 0)]
  rw [show ((0 : Int) : Rat) = (0 : Rat) from rfl]
  apply foldl_sum_congr_simple
  intro k _hk
  unfold castIntRow
  have hi_entry : (Vector.map (fun x : Int => (x : Rat)) (b.row i))[k] = ((b.row i)[k] : Rat) := by
    change (Vector.map (fun x : Int => (x : Rat)) (b.row i))[k.val] = ((b.row i)[k.val] : Rat)
    rw [Vector.getElem_map]
  have hj_entry : (Vector.map (fun x : Int => (x : Rat)) (b.row j))[k] = ((b.row j)[k] : Rat) := by
    change (Vector.map (fun x : Int => (x : Rat)) (b.row j))[k.val] = ((b.row j)[k.val] : Rat)
    rw [Vector.getElem_map]
  rw [hi_entry, hj_entry]
  rw [Rat.intCast_mul]

/-- The original-row coordinates chosen for the Gram-Schmidt prefix projection
solve the leading Gram linear system whose right-hand side is obtained by
dotting prefix rows with that projection. This is the matrix/vector form of
`originalProjectionCoords_dot_eq_gram_combination`; the downstream Cramer
bridge rewrites the right-hand side to the replacement Gram column. -/
private theorem scaledCoeffMatrix_replacementColumn_solve
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < i)
    (p : Fin (j + 1)) :
    (castIntDetMatrix
        (GramSchmidt.leadingGramMatrixInt b (j + 1)
          (Nat.succ_le_of_lt (Nat.lt_trans hj hi))) *
        originalProjectionCoords b i j hi (Nat.lt_trans hj hi))[p] =
        Matrix.dot
          (castIntRow b
            ⟨p.val, Nat.lt_of_lt_of_le p.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩)
          (basisPrefixProjection b i j hi (Nat.lt_trans hj hi)) := by
  have hsys :=
    originalProjectionCoords_dot_eq_gram_combination
      (b := b) (i := i) (j := j) (hi := hi)
      (hj := Nat.lt_trans hj hi) p
  change
    (Matrix.mulVec
        (castIntDetMatrix
          (GramSchmidt.leadingGramMatrixInt b (j + 1)
            (Nat.succ_le_of_lt (Nat.lt_trans hj hi))))
        (originalProjectionCoords b i j hi (Nat.lt_trans hj hi)))[p] =
      Matrix.dot
        (castIntRow b
          ⟨p.val, Nat.lt_of_lt_of_le p.isLt
            (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩)
        (basisPrefixProjection b i j hi (Nat.lt_trans hj hi))
  rw [hsys]
  unfold Matrix.mulVec Matrix.row
  have hleft :
      (Vector.ofFn fun i' : Fin (j + 1) =>
          Matrix.dot
            (castIntDetMatrix
              (GramSchmidt.leadingGramMatrixInt b (j + 1)
                (Nat.succ_le_of_lt (Nat.lt_trans hj hi))))[i']
            (originalProjectionCoords b i j hi (Nat.lt_trans hj hi)))[p] =
        Matrix.dot
          (castIntDetMatrix
            (GramSchmidt.leadingGramMatrixInt b (j + 1)
              (Nat.succ_le_of_lt (Nat.lt_trans hj hi))))[p]
          (originalProjectionCoords b i j hi (Nat.lt_trans hj hi)) := by
    simp [Vector.getElem_ofFn]
  rw [hleft]
  change
    (List.finRange (j + 1)).foldl
      (fun acc q =>
        acc +
          (castIntDetMatrix
            (GramSchmidt.leadingGramMatrixInt b (j + 1)
              (Nat.succ_le_of_lt (Nat.lt_trans hj hi))))[p][q] *
            (originalProjectionCoords b i j hi (Nat.lt_trans hj hi))[q]) 0 =
    (List.finRange (j + 1)).foldl
      (fun acc q =>
        acc +
          (originalProjectionCoords b i j hi (Nat.lt_trans hj hi))[q] *
            Matrix.dot
              (castIntRow b
                ⟨p.val, Nat.lt_of_lt_of_le p.isLt
                  (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩)
              (castIntRow b
                ⟨q.val, Nat.lt_of_lt_of_le q.isLt
                  (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩)) 0
  apply foldl_sum_congr_simple
  intro q _hq
  rw [castIntDetMatrix_get]
  simp [GramSchmidt.leadingGramMatrixInt, Matrix.ofFn, GramSchmidt.liftFinLE]
  rw [← dot_castIntRow_eq_cast_dot b
    (⟨p.val, Nat.lt_of_lt_of_le p.isLt
      (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩ : Fin n)
    (⟨q.val, Nat.lt_of_lt_of_le q.isLt
      (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩ : Fin n)]
  grind

/-- At `s = 0`, `progressMatrix` equals the entry-wise cast of
`leadingGramMatrixInt`. -/
private theorem progressMatrix_zero_eq_castIntDetMatrix (b : Matrix Int n m)
    (k : Nat) (hk : k ≤ n) :
    progressMatrix b k hk 0 =
      castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b k hk) := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro j hj
  let ii : Fin k := ⟨i, hi⟩
  let jj : Fin k := ⟨j, hj⟩
  change (progressMatrix b k hk 0)[ii][jj] =
    (castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b k hk))[ii][jj]
  have hjnlt : ¬ jj.val < 0 := Nat.not_lt_zero _
  rw [progressMatrix_get_ge b k hk 0 ii jj hjnlt]
  rw [castIntDetMatrix_get]
  -- LHS: Matrix.dot (castIntRow b (lift ii)) (castIntRow b (lift jj))
  -- RHS: ((leadingGramMatrixInt b k hk)[ii][jj] : Int : Rat)
  --   = (Matrix.dot (b.row (lift ii)) (b.row (lift jj)) : Int : Rat)
  rw [dot_castIntRow_eq_cast_dot]
  -- Match up the leadingGramMatrixInt entry definition.
  simp [GramSchmidt.leadingGramMatrixInt, Matrix.ofFn]

/-- `(gramDet b k hk : Rat)` equals the determinant of `progressMatrix` at the
starting index `s = 0`. -/
private theorem gramDet_rat_eq_progressMatrix_zero_det (b : Matrix Int n m)
    (k : Nat) (hk : k ≤ n) :
    (gramDet b k hk : Rat) = Matrix.det (progressMatrix b k hk 0) := by
  -- (gramDet b k hk : Rat) = ((Matrix.det leadingGramMatrixInt b k hk : Int) : Rat)
  -- via leadingGramMatrixInt_det_nonneg_pre + bareiss_eq_det.
  have hdet_int :
      Matrix.det (GramSchmidt.leadingGramMatrixInt b k hk) =
        Int.ofNat (gramDet b k hk) := by
    rw [gramDet, Matrix.bareiss_eq_det]
    exact (Int.toNat_of_nonneg (leadingGramMatrixInt_det_nonneg_pre b k hk)).symm
  have hstep1 : ((gramDet b k hk : Int) : Rat) =
      ((Matrix.det (GramSchmidt.leadingGramMatrixInt b k hk) : Int) : Rat) := by
    rw [hdet_int]
    rfl
  -- ((det leadingGramMatrixInt b k hk : Int) : Rat) = det (castIntDetMatrix _)
  -- via det_intCast.
  have hstep2 : ((Matrix.det (GramSchmidt.leadingGramMatrixInt b k hk) : Int) : Rat) =
      Matrix.det (castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b k hk)) :=
    det_intCast (GramSchmidt.leadingGramMatrixInt b k hk)
  -- det (castIntDetMatrix _) = det (progressMatrix b k hk 0) via progressMatrix_zero_eq.
  have hstep3 :
      Matrix.det (castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b k hk)) =
        Matrix.det (progressMatrix b k hk 0) := by
    rw [progressMatrix_zero_eq_castIntDetMatrix]
  -- Now (gramDet b k hk : Rat) = ((gramDet : Int) : Rat) by cast chain.
  have hcast_chain : ((gramDet b k hk : Nat) : Rat) =
      ((gramDet b k hk : Int) : Rat) := by
    push_cast; rfl
  rw [hcast_chain]
  rw [hstep1, hstep2, hstep3]

/-- Core proof of the Gram-determinant / squared-norm product bridge.

Chain: `(gramDet b k hk : Rat) = det (progressMatrix b k hk 0) =
det (progressMatrix b k hk k) = det (auxMatrix b k hk) = gramSchmidtNormProduct`.
Note: the proof does not use the independence hypothesis since both sides are
computed purely from `b`. The hypothesis is kept for parity with the public
theorem and downstream callers. -/
private theorem gramDet_eq_prod_normSq_core (b : Matrix Int n m)
    (_hli : independent b) (k : Nat) (hk : k ≤ n) :
    (gramDet b k hk : Rat) = gramSchmidtNormProduct b k hk := by
  rw [gramDet_rat_eq_progressMatrix_zero_det b k hk]
  rw [← progressMatrix_det_invariant b k hk k (Nat.le_refl k)]
  rw [progressMatrix_full_eq_auxMatrix]
  exact auxMatrix_det_eq_prod_normSq b k hk

theorem gramDet_eq_prod_normSq (b : Matrix Int n m)
    (hli : independent b) (k : Nat) (hk : k ≤ n) :
    (gramDet b k hk : Rat) = gramSchmidtNormProduct b k hk :=
  gramDet_eq_prod_normSq_core b hli k hk

theorem gramDet_pos (b : Matrix Int n m)
    (hli : independent b) (k : Nat) (hk : k ≤ n) (hk' : 0 < k) :
    0 < gramDet b k hk := by
  exact gramDet_pos_core b hli k hk hk'

/-- One-step extension of `gramSchmidtNormProduct`: appending the `k`-th
factor multiplies the `k`-fold product by `Vector.normSq ((basis b).row ⟨k, _⟩)`.
This is a `List.finRange` cancellation lemma; positivity of the leading Gram
determinant is handled separately by `gramDet_pos`. -/
private theorem gramSchmidtNormProduct_succ (b : Matrix Int n m)
    (k : Nat) (hk : k + 1 ≤ n) :
    gramSchmidtNormProduct b (k + 1) hk =
      gramSchmidtNormProduct b k (Nat.le_of_succ_le hk) *
        Vector.normSq ((basis b).row ⟨k, Nat.lt_of_succ_le hk⟩) := by
  unfold gramSchmidtNormProduct
  rw [List.finRange_succ_last]
  rw [List.foldl_append, List.foldl_map]
  simp only [List.foldl_cons, List.foldl_nil]
  rfl

private theorem basis_normSq_core (b : Matrix Int n m)
    (hli : independent b) (k : Nat) (hk : k < n) :
    Vector.normSq ((basis b).row ⟨k, hk⟩) =
      (gramDet b (k + 1) (Nat.succ_le_of_lt hk) : Rat) /
        (gramDet b k (Nat.le_of_lt hk) : Rat) := by
  have hk_le : k ≤ n := Nat.le_of_lt hk
  have hden_pos : 0 < (gramDet b k hk_le : Rat) := by
    rw [Rat.natCast_pos]
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0; rw [gramDet_zero]; decide
    · exact gramDet_pos b hli k hk_le hkpos
  have hprod_ne : gramSchmidtNormProduct b k hk_le ≠ 0 := by
    rw [← gramDet_eq_prod_normSq b hli k hk_le]
    exact Rat.ne_of_gt hden_pos
  rw [gramDet_eq_prod_normSq b hli (k + 1) (Nat.succ_le_of_lt hk)]
  rw [gramDet_eq_prod_normSq b hli k hk_le]
  rw [gramSchmidtNormProduct_succ b k (Nat.succ_le_of_lt hk)]
  rw [Rat.mul_comm]
  exact (Rat.mul_div_cancel hprod_ne).symm

theorem basis_normSq (b : Matrix Int n m)
    (hli : independent b) (k : Nat) (hk : k < n) :
    Vector.normSq ((basis b).row ⟨k, hk⟩) =
      (gramDet b (k + 1) (Nat.succ_le_of_lt hk) : Rat) /
        (gramDet b k (Nat.le_of_lt hk) : Rat) := by
  exact basis_normSq_core b hli k hk

/-- Original-row dot products vanish against orthogonal basis vectors of higher
index. For `p < r`, `castIntRow b p` lies in the basis-vector span of indices
`≤ p`, which is orthogonal to `(basis b).row r`. -/
private theorem dot_castIntRow_basis_eq_zero_of_lt
    (b : Matrix Int n m) (p r : Nat) (hp : p < n) (hr : r < n) (hpr : p < r) :
    Matrix.dot (castIntRow b ⟨p, hp⟩) ((basis b).row ⟨r, hr⟩) = 0 := by
  rw [dot_comm_rat]
  rw [castIntRow_decomposition b p hp]
  rw [dot_add_right_rat]
  have hbasis : Matrix.dot ((basis b).row ⟨r, hr⟩) ((basis b).row ⟨p, hp⟩) = 0 :=
    basis_orthogonal b r p hr hp (Nat.ne_of_gt hpr)
  have hprefix : Matrix.dot ((basis b).row ⟨r, hr⟩)
      (GramSchmidt.prefixCombination (coeffs b) (basis b) p hp) = 0 := by
    apply dot_prefixCombination_right_eq_zero_of_dot_zero
      (coeffs := coeffs b) (basisM := basis b) (i := p) (hi := hp)
      (u := (basis b).row ⟨r, hr⟩)
    intro p'
    have hp'_lt_p : p'.val < p := p'.isLt
    have hp'_lt_r : p'.val < r := Nat.lt_trans hp'_lt_p hpr
    have hp'_lt_n : p'.val < n := Nat.lt_trans hp'_lt_p hp
    exact basis_orthogonal b r p'.val hr hp'_lt_n (Nat.ne_of_gt hp'_lt_r)
  rw [hbasis, hprefix]
  grind

/-- Truncate a `Fin m` foldl to `Fin k₀` when the proof-indexed body vanishes
on indices `≥ k₀` and `k₀ ≤ m`. Induction is on `m`. -/
private theorem foldl_finRange_truncate_zero_above
    {n : Nat} (body : ∀ (k : Nat), k < n → Rat) (acc : Rat) (k₀ : Nat)
    (h_zero : ∀ r : Nat, k₀ ≤ r → (hrn : r < n) → body r hrn = 0) :
    ∀ (m : Nat) (hk : m ≤ n) (hkk : k₀ ≤ m),
      (List.finRange m).foldl
          (fun (acc' : Rat) (r : Fin m) =>
            acc' + body r.val (Nat.lt_of_lt_of_le r.isLt hk)) acc =
        (List.finRange k₀).foldl
          (fun (acc' : Rat) (q : Fin k₀) =>
            acc' + body q.val (Nat.lt_of_lt_of_le q.isLt (Nat.le_trans hkk hk))) acc := by
  intro m
  induction m with
  | zero =>
      intro _ hkk
      have hk₀ : k₀ = 0 := Nat.eq_zero_of_le_zero hkk
      subst hk₀
      rfl
  | succ m ih =>
      intro hk hkk
      rcases Nat.lt_or_ge m k₀ with hmk | hkm
      · have hk_eq : k₀ = m + 1 := Nat.le_antisymm hkk (Nat.succ_le_of_lt hmk)
        subst hk_eq
        rfl
      · have hk' : m ≤ n := Nat.le_of_succ_le hk
        have h_last_lt : m < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hk
        have h_last_zero : body m h_last_lt = 0 := h_zero m hkm h_last_lt
        rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
        simp only [List.foldl_cons, List.foldl_nil]
        have h_last :
            body (Fin.last m).val
                (Nat.lt_of_lt_of_le (Fin.last m).isLt hk) = 0 :=
          h_last_zero
        rw [h_last, Rat.add_zero]
        exact ih hk' hkm

/-- The Gram-Schmidt prefix projection of row `i` onto the span of rows
`0, ..., j` agrees with `castIntRow b i` when dotted with `castIntRow b p` for
any `p ≤ j < i`. The residue between the two lies in the span of basis vectors
of indices `> j`, hence orthogonal to `castIntRow b p`. -/
private theorem dot_castIntRow_castIntRow_eq_dot_basisPrefixProjection
    (b : Matrix Int n m) (i j p : Nat) (hi : i < n) (hj : j < i)
    (hp_le_j : p ≤ j) (hp : p < n) :
    Matrix.dot (castIntRow b ⟨p, hp⟩) (castIntRow b ⟨i, hi⟩) =
      Matrix.dot (castIntRow b ⟨p, hp⟩)
        (basisPrefixProjection b i j hi (Nat.lt_trans hj hi)) := by
  -- Substitute `i = (j + 1) + d` so the foldl bounds align with the helper.
  obtain ⟨d, rfl⟩ : ∃ d, i = (j + 1) + d := ⟨i - (j + 1), by omega⟩
  have hkdn : (j + 1) + d ≤ n := Nat.le_of_lt hi
  -- LHS via basis_decomposition for `castIntRow b i`.
  rw [castIntRow_decomposition b ((j + 1) + d) hi]
  rw [dot_add_right_rat]
  rw [dot_castIntRow_basis_eq_zero_of_lt b p ((j + 1) + d) hp hi
    (Nat.lt_of_le_of_lt hp_le_j hj)]
  rw [Rat.zero_add]
  rw [dot_prefixCombination_right_rat (coeffs := coeffs b) (basisM := basis b)
    (i := (j + 1) + d) (hi := hi) (u := castIntRow b ⟨p, hp⟩)]
  -- RHS unfold and expand basisPrefixProjection.
  unfold basisPrefixProjection
  rw [dot_rowCombination_right_rat]
  -- Define a Nat-indexed body shared by both sides.
  let body : ∀ (k : Nat), k < n → Rat := fun k hk =>
    GramSchmidt.entry (coeffs b) ⟨(j + 1) + d, hi⟩ ⟨k, hk⟩ *
      Matrix.dot (castIntRow b ⟨p, hp⟩) ((basis b).row ⟨k, hk⟩)
  -- Normalize the RHS foldl body to use `body`. The literal proof inside the
  -- unfolded `basisPrefixProjection` is `Nat.lt_trans hj hi`.
  have hRHS :
      (List.finRange (j + 1)).foldl
          (fun (acc' : Rat) (q : Fin (j + 1)) =>
            acc' +
              (projectionCoeffPrefix b ((j + 1) + d) j hi
                (Nat.lt_trans hj hi))[q] *
              Matrix.dot (castIntRow b ⟨p, hp⟩)
                ((GramSchmidt.prefixRows (basis b) j (Nat.lt_trans hj hi)).row q)) 0 =
        (List.finRange (j + 1)).foldl
          (fun (acc' : Rat) (q : Fin (j + 1)) =>
            acc' + body q.val (Nat.lt_of_lt_of_le q.isLt
              (Nat.le_trans (Nat.le_add_right (j + 1) d) hkdn))) 0 := by
    apply foldl_sum_congr_simple
    intro q _hq
    have hq_lt_n : q.val < n :=
      Nat.lt_of_lt_of_le q.isLt (Nat.le_trans (Nat.le_add_right (j + 1) d) hkdn)
    have hcoeff :
        (projectionCoeffPrefix b ((j + 1) + d) j hi (Nat.lt_trans hj hi))[q] =
          GramSchmidt.entry (coeffs b) ⟨(j + 1) + d, hi⟩ ⟨q.val, hq_lt_n⟩ := by
      simp [projectionCoeffPrefix, Vector.getElem_ofFn]
    have hrow :
        (GramSchmidt.prefixRows (basis b) j (Nat.lt_trans hj hi)).row q =
          (basis b).row ⟨q.val, hq_lt_n⟩ := by
      simp [GramSchmidt.prefixRows, Matrix.row, Vector.getElem_ofFn]
    rw [hcoeff, hrow]
  rw [hRHS]
  -- Apply foldl truncation. By proof irrelevance the LHS body matches.
  exact foldl_finRange_truncate_zero_above body 0 (j + 1)
    (by
      intro r hjr hrn
      show GramSchmidt.entry (coeffs b) ⟨(j + 1) + d, hi⟩ ⟨r, hrn⟩ *
          Matrix.dot (castIntRow b ⟨p, hp⟩) ((basis b).row ⟨r, hrn⟩) = 0
      have hpr : p < r := Nat.lt_of_le_of_lt hp_le_j (Nat.lt_of_succ_le hjr)
      rw [dot_castIntRow_basis_eq_zero_of_lt b p r hp hrn hpr]
      grind)
    ((j + 1) + d) hkdn (Nat.le_add_right (j + 1) d)

private theorem dot_basisPrefixProjection_eq_castIntGram
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < i)
    (p : Fin (j + 1)) :
    Matrix.dot
        (castIntRow b
          ⟨p.val, Nat.lt_of_lt_of_le p.isLt
            (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩)
        (basisPrefixProjection b i j hi (Nat.lt_trans hj hi)) =
      ((Matrix.dot
          (b.row
            ⟨p.val, Nat.lt_of_lt_of_le p.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩)
          (b.row ⟨i, hi⟩) : Int) : Rat) := by
  rw [← dot_castIntRow_eq_cast_dot b
    (⟨p.val, Nat.lt_of_lt_of_le p.isLt
      (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩ : Fin n)
    (⟨i, hi⟩ : Fin n)]
  exact
    (dot_castIntRow_castIntRow_eq_dot_basisPrefixProjection
      b i j p.val hi hj (Nat.le_of_lt_succ p.isLt)
      (Nat.lt_of_lt_of_le p.isLt
        (Nat.succ_le_of_lt (Nat.lt_trans hj hi)))).symm

private theorem scaledCoeffMatrix_replacementColumn_solve_intGram
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < i)
    (p : Fin (j + 1)) :
    (castIntDetMatrix
        (GramSchmidt.leadingGramMatrixInt b (j + 1)
          (Nat.succ_le_of_lt (Nat.lt_trans hj hi))) *
        originalProjectionCoords b i j hi (Nat.lt_trans hj hi))[p] =
      ((Matrix.dot
          (b.row
            ⟨p.val, Nat.lt_of_lt_of_le p.isLt
              (Nat.succ_le_of_lt (Nat.lt_trans hj hi))⟩)
          (b.row ⟨i, hi⟩) : Int) : Rat) := by
  rw [scaledCoeffMatrix_replacementColumn_solve b i j hi hj p]
  exact dot_basisPrefixProjection_eq_castIntGram b i j hi hj p

/-- Isolate the last term in a `foldl` over `List.finRange (k + 1)` when every
earlier term vanishes. -/
private theorem foldl_finRange_succ_isolate_last
    (k : Nat) (f : Fin (k + 1) → Rat)
    (h_zero : ∀ q : Fin (k + 1), q.val < k → f q = 0) :
    (List.finRange (k + 1)).foldl
        (fun (acc : Rat) (q : Fin (k + 1)) => acc + f q) 0 =
      f (Fin.last k) := by
  rw [List.finRange_succ_last, List.foldl_append, List.foldl_map]
  simp only [List.foldl_cons, List.foldl_nil]
  have hfold_zero :
      (List.finRange k).foldl
          (fun (acc : Rat) (q : Fin k) => acc + f (Fin.castSucc q)) 0 = 0 := by
    have hgen : ∀ (xs : List (Fin k)) (acc : Rat),
        xs.foldl (fun acc' q => acc' + f (Fin.castSucc q)) acc = acc := by
      intro xs
      induction xs with
      | nil => intro acc; rfl
      | cons q xs ih =>
          intro acc
          simp only [List.foldl_cons]
          have hq : f (Fin.castSucc q) = 0 := h_zero (Fin.castSucc q) q.isLt
          rw [hq, Rat.add_zero]
          exact ih acc
    exact hgen (List.finRange k) 0
  rw [hfold_zero, Rat.zero_add]

/-- Dotting `basisPrefixProjection b i j` with the Gram-Schmidt basis vector
`(basis b).row ⟨j, _⟩` extracts the projection coefficient `coeffs[i][j]`,
weighted by `(basis b).row j`'s squared norm. -/
private theorem dot_basis_basisPrefixProjection_eq_coeff_mul_normSq
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < i) :
    Matrix.dot ((basis b).row ⟨j, Nat.lt_trans hj hi⟩)
        (basisPrefixProjection b i j hi (Nat.lt_trans hj hi)) =
      GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ *
        Vector.normSq ((basis b).row ⟨j, Nat.lt_trans hj hi⟩) := by
  have hjlt : j < n := Nat.lt_trans hj hi
  unfold basisPrefixProjection
  rw [dot_rowCombination_right_rat]
  -- Isolate the q = ⟨j, lt_succ_self j⟩ term in the foldl.
  rw [foldl_finRange_succ_isolate_last j _ ?_]
  · -- Last term: projectionCoeffPrefix[⟨j, _⟩] * dot basis[j] basis[j].
    have hrow :
        (GramSchmidt.prefixRows (basis b) j hjlt).row (Fin.last j) =
          (basis b).row ⟨j, hjlt⟩ := by
      simp [GramSchmidt.prefixRows, Matrix.row, Vector.getElem_ofFn, Fin.last]
    have hcoeff :
        (projectionCoeffPrefix b i j hi hjlt)[Fin.last j] =
          GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, hjlt⟩ := by
      simp [projectionCoeffPrefix, Vector.getElem_ofFn, Fin.last]
    rw [hcoeff, hrow]
    rfl
  · -- For q < j: dot basis[j] basis[q.val_lift] = 0.
    intro q hqval
    have hq_lt_n : q.val < n :=
      Nat.lt_of_lt_of_le q.isLt (Nat.succ_le_of_lt hjlt)
    have hrow :
        (GramSchmidt.prefixRows (basis b) j hjlt).row q =
          (basis b).row ⟨q.val, hq_lt_n⟩ := by
      simp [GramSchmidt.prefixRows, Matrix.row, Vector.getElem_ofFn]
    rw [hrow]
    rw [basis_orthogonal b j q.val hjlt hq_lt_n (Nat.ne_of_gt hqval)]
    grind

/-- Dotting `basisPrefixProjection b i j` with `(basis b).row ⟨j, _⟩` also
extracts the original-row coordinate, weighted by the squared norm. -/
private theorem dot_basis_basisPrefixProjection_eq_origProjCoords_mul_normSq
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < i) :
    Matrix.dot ((basis b).row ⟨j, Nat.lt_trans hj hi⟩)
        (basisPrefixProjection b i j hi (Nat.lt_trans hj hi)) =
      (originalProjectionCoords b i j hi (Nat.lt_trans hj hi))[Fin.last j] *
        Vector.normSq ((basis b).row ⟨j, Nat.lt_trans hj hi⟩) := by
  have hjlt : j < n := Nat.lt_trans hj hi
  rw [← originalProjectionCoords_spec b i j hi hjlt]
  rw [dot_rowCombination_right_rat]
  rw [foldl_finRange_succ_isolate_last j _ ?_]
  · -- Last term: origProjCoords[⟨j, _⟩] * dot basis[j] (cast b row j).
    -- castIntMatrixRat b row at ⟨j, _⟩ = castIntRow b ⟨j, _⟩.
    have hrow :
        (GramSchmidt.prefixRows (castIntMatrixRat b) j hjlt).row (Fin.last j) =
          castIntRow b ⟨j, hjlt⟩ := by
      simp [GramSchmidt.prefixRows, Matrix.row, Vector.getElem_ofFn,
        castIntMatrixRat, castIntRow, Fin.last]
    rw [hrow]
    -- dot basis[j] castIntRow b j = dot basis[j] (basis[j] + prefixComb) = normSq + 0.
    rw [castIntRow_decomposition b j hjlt]
    rw [dot_add_right_rat]
    have hbasis_self :
        Matrix.dot ((basis b).row ⟨j, hjlt⟩) ((basis b).row ⟨j, hjlt⟩) =
          Vector.normSq ((basis b).row ⟨j, hjlt⟩) := rfl
    rw [hbasis_self]
    have hprefix :
        Matrix.dot ((basis b).row ⟨j, hjlt⟩)
            (GramSchmidt.prefixCombination (coeffs b) (basis b) j hjlt) = 0 := by
      apply dot_prefixCombination_right_eq_zero_of_dot_zero
        (coeffs := coeffs b) (basisM := basis b) (i := j) (hi := hjlt)
        (u := (basis b).row ⟨j, hjlt⟩)
      intro r
      have hr_lt_j : r.val < j := r.isLt
      have hr_lt_n : r.val < n := Nat.lt_trans hr_lt_j hjlt
      exact basis_orthogonal b j r.val hjlt hr_lt_n (Nat.ne_of_gt hr_lt_j)
    rw [hprefix, Rat.add_zero]
  · -- For q < j: dot basis[j] castIntRow b q = 0.
    intro q hqval
    have hq_lt_n : q.val < n :=
      Nat.lt_of_lt_of_le q.isLt (Nat.succ_le_of_lt hjlt)
    have hrow :
        (GramSchmidt.prefixRows (castIntMatrixRat b) j hjlt).row q =
          castIntRow b ⟨q.val, hq_lt_n⟩ := by
      simp [GramSchmidt.prefixRows, Matrix.row, Vector.getElem_ofFn,
        castIntMatrixRat, castIntRow]
    rw [hrow]
    rw [dot_comm_rat]
    rw [dot_castIntRow_basis_eq_zero_of_lt b q.val j hq_lt_n hjlt hqval]
    grind

/-- The Gram-determinant succession: `(gramDet (j+1) : Rat)` factors as
`(gramSchmidtNormProduct j) * normSq(basis[j])`. -/
private theorem gramDet_succ_rat
    (b : Matrix Int n m) (j : Nat) (hjsuc : j + 1 ≤ n) :
    (gramDet b (j + 1) hjsuc : Rat) =
      gramSchmidtNormProduct b j (Nat.le_of_succ_le hjsuc) *
        Vector.normSq ((basis b).row ⟨j, Nat.lt_of_succ_le hjsuc⟩) := by
  have hgd_eq_gsnp :
      (gramDet b (j + 1) hjsuc : Rat) = gramSchmidtNormProduct b (j + 1) hjsuc := by
    rw [gramDet_rat_eq_progressMatrix_zero_det]
    rw [← progressMatrix_det_invariant b (j + 1) hjsuc (j + 1) (Nat.le_refl _)]
    rw [progressMatrix_full_eq_auxMatrix]
    exact auxMatrix_det_eq_prod_normSq b (j + 1) hjsuc
  rw [hgd_eq_gsnp]
  exact gramSchmidtNormProduct_succ b j hjsuc

/-- Cramer's-rule bridge for the scaled Gram-Schmidt coefficient determinant:
the Leibniz determinant of `scaledCoeffMatrix` equals
`gramDet b (j + 1) * coeffs[i,j]` after casting to `Rat`. -/
private theorem scaledCoeffMatrix_det_eq_gramDet_mul_coeffs
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < i) :
    ((Matrix.det
        (GramSchmidt.scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ hj) :
          Int) : Rat) =
      (gramDet b (j + 1) (Nat.succ_le_of_lt (Nat.lt_trans hj hi)) : Rat) *
        GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ := by
  have hjlt : j < n := Nat.lt_trans hj hi
  have hjsuc : j + 1 ≤ n := Nat.succ_le_of_lt hjlt
  -- Cast LHS via det_intCast.
  rw [det_intCast]
  -- Step 1: express `castIntDetMatrix M` as a `colReplace` of `castIntDetMatrix G`.
  have hM_colReplace :
      castIntDetMatrix
          (GramSchmidt.scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, hjlt⟩ hj) =
        Matrix.colReplace
          (castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc))
          (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1))
          (fun p : Fin (j + 1) =>
            Matrix.dot
              (castIntRow b ⟨p.val, Nat.lt_of_lt_of_le p.isLt hjsuc⟩)
              (castIntRow b ⟨i, hi⟩)) := by
    apply Vector.ext
    intro r hr
    apply Vector.ext
    intro c hc
    let pp : Fin (j + 1) := ⟨r, hr⟩
    let cc : Fin (j + 1) := ⟨c, hc⟩
    change
      (castIntDetMatrix
          (GramSchmidt.scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, hjlt⟩ hj))[pp][cc] =
        (Matrix.colReplace _ _ _)[pp][cc]
    rw [Matrix.colReplace_get, castIntDetMatrix_get]
    by_cases hc_eq : cc = (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1))
    · rw [if_pos hc_eq]
      have hc_val : cc.val = j := congrArg Fin.val hc_eq
      have hsc :
          (GramSchmidt.scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, hjlt⟩ hj)[pp][cc] =
            Matrix.dot
              (b.row ⟨pp.val, Nat.lt_of_lt_of_le pp.isLt hjsuc⟩)
              (b.row ⟨i, hi⟩) := by
        simp [GramSchmidt.scaledCoeffMatrix, Matrix.ofFn,
          GramSchmidt.liftFinLE, hc_val]
      rw [hsc, ← dot_castIntRow_eq_cast_dot]
    · rw [if_neg hc_eq, castIntDetMatrix_get]
      have hc_ne : cc.val ≠ j := fun h => hc_eq (Fin.ext h)
      have hsc :
          (GramSchmidt.scaledCoeffMatrix b ⟨i, hi⟩ ⟨j, hjlt⟩ hj)[pp][cc] =
            Matrix.dot
              (b.row ⟨pp.val, Nat.lt_of_lt_of_le pp.isLt hjsuc⟩)
              (b.row ⟨cc.val, Nat.lt_of_lt_of_le cc.isLt hjsuc⟩) := by
        simp [GramSchmidt.scaledCoeffMatrix, Matrix.ofFn,
          GramSchmidt.liftFinLE, hc_ne]
      have hG :
          (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc)[pp][cc] =
            Matrix.dot
              (b.row ⟨pp.val, Nat.lt_of_lt_of_le pp.isLt hjsuc⟩)
              (b.row ⟨cc.val, Nat.lt_of_lt_of_le cc.isLt hjsuc⟩) := by
        simp [GramSchmidt.leadingGramMatrixInt, Matrix.ofFn,
          GramSchmidt.liftFinLE]
      rw [hsc, hG]
  rw [hM_colReplace]
  -- Step 2: rewrite the replacement column as `castG * originalProjectionCoords`.
  have hcol_lin_comb :
      (fun p : Fin (j + 1) =>
        Matrix.dot
          (castIntRow b ⟨p.val, Nat.lt_of_lt_of_le p.isLt hjsuc⟩)
          (castIntRow b ⟨i, hi⟩)) =
      (fun p : Fin (j + 1) =>
        (List.finRange (j + 1)).foldl
          (fun (acc : Rat) (q : Fin (j + 1)) =>
            acc + (originalProjectionCoords b i j hi hjlt)[q] *
              (castIntDetMatrix
                (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc))[p][q]) 0) := by
    funext p
    -- dot castIntRow b p castIntRow b i = dot castIntRow b p basisPrefixProjection
    rw [dot_castIntRow_castIntRow_eq_dot_basisPrefixProjection b i j p.val hi hj
      (Nat.le_of_lt_succ p.isLt) (Nat.lt_of_lt_of_le p.isLt hjsuc)]
    -- = (castG * originalProjectionCoords)[p]
    rw [← scaledCoeffMatrix_replacementColumn_solve b i j hi hj p]
    -- Now: (castG * origProjCoords)[p] = foldl over Fin (j+1) of castG[p][q] * origProjCoords[q].
    -- Reorder to origProjCoords[q] * castG[p][q] using Rat.mul_comm.
    change
      (Matrix.mulVec
          (castIntDetMatrix
            (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc))
          (originalProjectionCoords b i j hi hjlt))[p] = _
    unfold Matrix.mulVec Matrix.row
    have hleft :
        (Vector.ofFn fun i' : Fin (j + 1) =>
            Matrix.dot
              (castIntDetMatrix
                (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc))[i']
              (originalProjectionCoords b i j hi hjlt))[p] =
          Matrix.dot
            (castIntDetMatrix
              (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc))[p]
            (originalProjectionCoords b i j hi hjlt) := by
      simp [Vector.getElem_ofFn]
    rw [hleft]
    unfold Matrix.dot Hex.Vector.dotProduct
    apply foldl_sum_congr_simple
    intro q _hq
    grind
  rw [hcol_lin_comb]
  -- Step 3: apply det_colReplace_sum_finRange.
  rw [Matrix.det_colReplace_sum_finRange]
  -- Step 4: isolate the q = ⟨j, _⟩ term.
  rw [foldl_finRange_succ_isolate_last j _ ?_]
  · -- Last term: origProjCoords[⟨j, _⟩] * det castG.
    have hlast_self :
        Matrix.colReplace
            (castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc))
            (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1))
            (fun p : Fin (j + 1) =>
              (castIntDetMatrix
                (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc))[p][Fin.last j]) =
          castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc) :=
      Matrix.colReplace_self _ _
    rw [hlast_self]
    -- det castG = (gramDet (j+1) : Rat).
    have hdetG :
        Matrix.det
            (castIntDetMatrix (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc)) =
          (gramDet b (j + 1) hjsuc : Rat) := by
      rw [← det_intCast]
      have hdet_int :
          Matrix.det (GramSchmidt.leadingGramMatrixInt b (j + 1) hjsuc) =
            Int.ofNat (gramDet b (j + 1) hjsuc) := by
        rw [gramDet, Matrix.bareiss_eq_det]
        exact (Int.toNat_of_nonneg
          (leadingGramMatrixInt_det_nonneg_pre b (j + 1) hjsuc)).symm
      rw [hdet_int]
      push_cast
      rfl
    rw [hdetG]
    -- Cancellation: origProjCoords[Fin.last j] * gramDet = gramDet * coeffs[i][j].
    have hcancel_normSq :
        Vector.normSq ((basis b).row ⟨j, hjlt⟩) *
            (originalProjectionCoords b i j hi hjlt)[Fin.last j] =
          Vector.normSq ((basis b).row ⟨j, hjlt⟩) *
            GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, hjlt⟩ := by
      have hH2 := dot_basis_basisPrefixProjection_eq_coeff_mul_normSq b i j hi hj
      have hH3 := dot_basis_basisPrefixProjection_eq_origProjCoords_mul_normSq b i j hi hj
      have heq := hH3.symm.trans hH2
      -- heq : (originalProjectionCoords ...)[Fin.last j] * normSq = entry coeffs ... * normSq
      grind
    have hgd_succ := gramDet_succ_rat b j hjsuc
    -- Combine: gramDet(j+1) * coeffs[i][j] = gnp(j) * normSq * coeffs[i][j] = gnp(j) * normSq * origProjCoords = gramDet(j+1) * origProjCoords.
    rw [hgd_succ]
    have hgnp_ne_or_zero :
        gramSchmidtNormProduct b j (Nat.le_of_succ_le hjsuc) *
              Vector.normSq ((basis b).row ⟨j, hjlt⟩) *
            (originalProjectionCoords b i j hi hjlt)[Fin.last j] =
          gramSchmidtNormProduct b j (Nat.le_of_succ_le hjsuc) *
              Vector.normSq ((basis b).row ⟨j, hjlt⟩) *
            GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, hjlt⟩ := by
      have h1 :
          gramSchmidtNormProduct b j (Nat.le_of_succ_le hjsuc) *
              Vector.normSq ((basis b).row ⟨j, hjlt⟩) *
            (originalProjectionCoords b i j hi hjlt)[Fin.last j] =
            gramSchmidtNormProduct b j (Nat.le_of_succ_le hjsuc) *
              (Vector.normSq ((basis b).row ⟨j, hjlt⟩) *
                (originalProjectionCoords b i j hi hjlt)[Fin.last j]) := by
        grind
      have h2 :
          gramSchmidtNormProduct b j (Nat.le_of_succ_le hjsuc) *
              Vector.normSq ((basis b).row ⟨j, hjlt⟩) *
            GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, hjlt⟩ =
            gramSchmidtNormProduct b j (Nat.le_of_succ_le hjsuc) *
              (Vector.normSq ((basis b).row ⟨j, hjlt⟩) *
                GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, hjlt⟩) := by
        grind
      rw [h1, h2, hcancel_normSq]
    rw [Rat.mul_comm (originalProjectionCoords b i j hi hjlt)[Fin.last j] _]
    exact hgnp_ne_or_zero
  · -- For q < j: det (colReplace castG ⟨j, _⟩ (col q of castG)) = 0 (existing col).
    intro q hqval
    have hq_ne :
        q ≠ (⟨j, Nat.lt_succ_self j⟩ : Fin (j + 1)) := by
      intro h
      exact Nat.ne_of_lt hqval (congrArg Fin.val h)
    rw [Matrix.det_colReplace_existing_col_eq_zero _ _ _ hq_ne]
    grind

/-- The fraction-free scaled-coefficient loop computes the Cramer/Bareiss
integer equal to `d[j+1] * μ[i,j]` below the diagonal. -/
private theorem scaledCoeffRows_lower_eq_coeffs
    (b : Matrix Int n m) (i j : Nat) (hi : i < n) (hj : j < i) :
    ((getArrayEntry (scaledCoeffRows b) i j : Int) : Rat) =
      (gramDet b (j + 1) (Nat.succ_le_of_lt (Nat.lt_trans hj hi)) : Rat) *
        GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ := by
  rw [scaledCoeffRows_lower_eq_scaledCoeffMatrix_bareiss (b := b) i j hi hj]
  rw [scaledCoeffMatrix_bareiss_eq_det (b := b) i j hi hj]
  exact scaledCoeffMatrix_det_eq_gramDet_mul_coeffs (b := b) i j hi hj

theorem scaledCoeffs_eq (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < i) :
    ((GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ : Int) : Rat) =
      (gramDet b (j + 1) (Nat.succ_le_of_lt (Nat.lt_trans hj hi)) : Rat) *
        GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ := by
  simpa [scaledCoeffs, data, rowsToMatrix, GramSchmidt.entry, Matrix.row, Matrix.ofFn] using
    scaledCoeffRows_lower_eq_coeffs (b := b) i j hi hj

theorem scaledCoeffs_diag (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨i, hi⟩ =
      Int.ofNat (gramDet b (i + 1) (Nat.succ_le_of_lt hi)) := by
  simpa [scaledCoeffs, data, rowsToMatrix, GramSchmidt.entry, Matrix.row, Matrix.ofFn] using
    scaledCoeffRows_diag_eq_gramDet (b := b) i hi

theorem scaledCoeffs_upper (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i < j) :
    GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨j, hj⟩ = 0 := by
  simpa [scaledCoeffs, data, rowsToMatrix, scaledCoeffRows, GramSchmidt.entry, Matrix.row,
    Matrix.ofFn] using getArrayEntry_scaledCoeffArrayLoop_above n n
    { step := 0
      matrix := gramRows b
      coeffs := zeroRows n
      prevPivot := 1 }
    (by
      intro r c hrc
      exact getArrayEntry_zeroRows n r c)
    i j hij

/-- Below the diagonal, the executable integral scaled coefficient is exactly
the Cramer determinant encoded by `scaledCoeffMatrix`. -/
theorem scaledCoeffs_eq_scaledCoeffMatrix_det
    (b : Matrix Int n m) (i j : Fin n) (hji : j.val < i.val) :
    GramSchmidt.entry (scaledCoeffs b) i j =
      Matrix.det (GramSchmidt.scaledCoeffMatrix b i j hji) := by
  have h :
      getArrayEntry (scaledCoeffRows b) i.val j.val =
        Matrix.det (GramSchmidt.scaledCoeffMatrix b i j hji) := by
    rw [scaledCoeffRows_lower_eq_scaledCoeffMatrix_bareiss
      (b := b) i.val j.val i.isLt hji]
    exact Matrix.bareiss_eq_det
      (GramSchmidt.scaledCoeffMatrix b i j hji)
  simpa [scaledCoeffs, data, rowsToMatrix, GramSchmidt.entry, Matrix.row, Matrix.ofFn] using h

/-- Leading integer Gram determinants are nonnegative. -/
theorem leadingGramMatrixInt_det_nonneg
    (b : Matrix Int n m) (t : Nat) (ht : t ≤ n) :
    0 ≤ Matrix.det (GramSchmidt.leadingGramMatrixInt b t ht) := by
  let rowPrefix : Matrix Int t m :=
    Matrix.ofFn fun i j =>
      (b.row ⟨i.val, Nat.lt_of_lt_of_le i.isLt ht⟩)[j]
  have hgram :
      GramSchmidt.leadingGramMatrixInt b t ht =
        Matrix.gramMatrix rowPrefix := by
    apply Vector.ext
    intro i hi
    apply Vector.ext
    intro j hj
    simp [GramSchmidt.leadingGramMatrixInt, rowPrefix, Matrix.gramMatrix, Matrix.dot,
      Matrix.row, Matrix.ofFn, GramSchmidt.liftFinLE]
  rw [hgram]
  exact Matrix.det_gramMatrix_nonneg rowPrefix

/-- Conditional form of the leading Gram determinant bridge. The remaining
unconditional bridge is exactly the nonnegativity of leading Gram determinants:
once `0 ≤ det` is available, the public `Nat`-valued `gramDet` casts back to
the signed determinant. -/
theorem leadingGramMatrixInt_det_eq_gramDet_int_of_nonneg
    (b : Matrix Int n m) (t : Nat) (ht : t ≤ n)
    (hdet : 0 ≤ Matrix.det (GramSchmidt.leadingGramMatrixInt b t ht)) :
    Matrix.det (GramSchmidt.leadingGramMatrixInt b t ht) =
      Int.ofNat (gramDet b t ht) := by
  rw [gramDet, Matrix.bareiss_eq_det]
  exact (Int.toNat_of_nonneg hdet).symm

/-- The public `Nat` Gram determinant casts back to the signed determinant of
the leading integer Gram matrix. -/
theorem leadingGramMatrixInt_det_eq_gramDet_int
    (b : Matrix Int n m) (t : Nat) (ht : t ≤ n) :
    Matrix.det (GramSchmidt.leadingGramMatrixInt b t ht) =
      Int.ofNat (gramDet b t ht) :=
  leadingGramMatrixInt_det_eq_gramDet_int_of_nonneg b t ht
    (leadingGramMatrixInt_det_nonneg b t ht)

theorem normSq_latticeVec_ge_min_basis_normSq
    (b : Matrix Int n m) (hli : independent b)
    (v : Vector Int m) (hv : memLattice b v) (hv' : v ≠ 0) :
    ∃ i : Fin n,
      Vector.normSq ((basis b).row i) ≤ ((Vector.normSq v : Int) : Rat) := by
  sorry

/-! ### Row-add invariance of the leading Gram determinant

The remaining theorems show that adding a multiple of an earlier row to a later
row leaves `gramDet` unchanged. Concretely, when `j.val < k.val` and the
modified row `k` lies inside the leading `t`-prefix, the leading Gram matrix
acquires a `rowAdd`-then-`colAdd` decoration at the corresponding `Fin t`
indices; both operations preserve determinants. When `t ≤ k.val`, the leading
prefix is untouched. -/

/-- Entry-level expansion of `Matrix.rowAdd` for a rectangular matrix. -/
private theorem rowAdd_get_rect {R : Type u} [Mul R] [Add R] {n' m' : Nat}
    (M : Matrix R n' m') (src dst r : Fin n') (c : R) (k : Fin m') :
    (Matrix.rowAdd M src dst c)[r][k] =
      if r = dst then M[dst][k] + c * M[src][k] else M[r][k] := by
  by_cases h : r = dst
  · subst r
    simp [Matrix.rowAdd]
  · simp [Matrix.rowAdd, h]
    have hval : dst.val ≠ r.val := by
      intro hval
      exact h (Fin.ext hval.symm)
    have hrow :
        (M.set dst (Vector.ofFn fun k => M[dst][k] + c * M[src][k]))[r] = M[r] :=
      (Vector.getElem_set_ne (xs := M)
        (x := Vector.ofFn fun k => M[dst][k] + c * M[src][k])
        dst.isLt r.isLt hval)
    simpa [Matrix.rowAdd] using congrArg (fun row => row[k]) hrow

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
    simpa [Matrix.row] using hget
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

/-- A row of `Matrix.rowAdd M src dst c` away from `dst` is unchanged. -/
private theorem rowAdd_row_eq_of_ne {R : Type u} [Mul R] [Add R] {n' m' : Nat}
    (M : Matrix R n' m') (src dst r : Fin n') (c : R) (hr : r.val ≠ dst.val) :
    (Matrix.rowAdd M src dst c)[r] = M[r] :=
  Vector.getElem_set_ne (xs := M)
    (x := Vector.ofFn fun k => M[dst][k] + c * M[src][k])
    dst.isLt r.isLt (fun heq => hr heq.symm)

/-- The row of `Matrix.rowAdd M src dst c` at index `dst` is the entry-wise
sum `M[dst] + c * M[src]`. -/
private theorem rowAdd_row_at {R : Type u} [Mul R] [Add R] {n' m' : Nat}
    (M : Matrix R n' m') (src dst : Fin n') (c : R) :
    (Matrix.rowAdd M src dst c)[dst] =
      Vector.ofFn fun k => M[dst][k] + c * M[src][k] := by
  unfold Matrix.rowAdd
  simp

/-- Inductive helper for `dot_rowAdd_row_at_left`: distribution along a foldl. -/
private theorem foldl_dot_rowAdd_at {n' m' : Nat}
    (M : Matrix Int n' m') (src dst : Fin n') (c : Int) (w : Vector Int m')
    (xs : List (Fin m')) (acc accX accY : Int) (hacc : acc = accX + c * accY) :
    xs.foldl (fun a i => a + (Matrix.rowAdd M src dst c)[dst][i] * w[i]) acc =
      xs.foldl (fun a i => a + M[dst][i] * w[i]) accX +
        c * xs.foldl (fun a i => a + M[src][i] * w[i]) accY := by
  induction xs generalizing acc accX accY with
  | nil =>
      simpa using hacc
  | cons i xs ih =>
      simp only [List.foldl_cons]
      apply ih
      have hentry : (Matrix.rowAdd M src dst c)[dst][i] = M[dst][i] + c * M[src][i] := by
        rw [rowAdd_get_rect]
        simp
      rw [hentry, hacc]
      grind

/-- Distribute dot product on the left over the row produced by
`Matrix.rowAdd`: at index `dst`, the row is `M[dst] + c * M[src]` componentwise,
so dot with `w` distributes over the sum. -/
private theorem dot_rowAdd_row_at_left {n' m' : Nat}
    (M : Matrix Int n' m') (src dst : Fin n') (c : Int) (w : Vector Int m') :
    Matrix.dot ((Matrix.rowAdd M src dst c)[dst]) w =
      Matrix.dot M[dst] w + c * Matrix.dot M[src] w := by
  simp only [Matrix.dot, Hex.Vector.dotProduct]
  exact foldl_dot_rowAdd_at M src dst c w (List.finRange m')
    0 0 0 (by show (0 : Int) = 0 + c * 0; grind)

/-- Symmetric form: dot product on the right with the modified row. -/
private theorem dot_rowAdd_row_at_right {n' m' : Nat}
    (M : Matrix Int n' m') (src dst : Fin n') (c : Int) (w : Vector Int m') :
    Matrix.dot w ((Matrix.rowAdd M src dst c)[dst]) =
      Matrix.dot w M[dst] + c * Matrix.dot w M[src] := by
  rw [dot_comm_int w, dot_rowAdd_row_at_left, dot_comm_int w M[dst], dot_comm_int w M[src]]

/-- Determinant-level pivot bridge for scaled Gram-Schmidt coefficients under
an elementary row addition. In the Cramer matrix computing `nu[k,j]`, replacing
row `k` by `row k + c * row j` changes the replaced last column linearly: the
new determinant is the old Cramer determinant plus `c` times the leading Gram
determinant. This formulation does not require the rational coefficient
denominator to be nonzero. -/
theorem scaledCoeffMatrix_rowAdd_pivot_det
    (b : Matrix Int n m) (j k : Fin n) (hjk : j.val < k.val) (c : Int) :
    Matrix.det (GramSchmidt.scaledCoeffMatrix (Matrix.rowAdd b j k c) k j hjk) =
      Matrix.det (GramSchmidt.scaledCoeffMatrix b k j hjk) +
        c * Matrix.det
          (GramSchmidt.leadingGramMatrixInt b (j.val + 1) (Nat.succ_le_of_lt j.isLt)) := by
  let t := j.val + 1
  let ht : t ≤ n := Nat.succ_le_of_lt j.isLt
  let last : Fin t := ⟨j.val, Nat.lt_succ_self j.val⟩
  let M := GramSchmidt.leadingGramMatrixInt b t ht
  let oldCol : Fin t → Int := fun p =>
    Matrix.dot (b.row (GramSchmidt.liftFinLE p ht)) (b.row k)
  let gramCol : Fin t → Int := fun p =>
    Matrix.dot (b.row (GramSchmidt.liftFinLE p ht)) (b.row j)
  have hnew :
      GramSchmidt.scaledCoeffMatrix (Matrix.rowAdd b j k c) k j hjk =
        Matrix.colReplace M last (fun p => oldCol p + c * gramCol p) := by
    apply Vector.ext
    intro r hr
    apply Vector.ext
    intro q hq
    let p : Fin t := ⟨r, hr⟩
    let qf : Fin t := ⟨q, hq⟩
    have hp_ne : (GramSchmidt.liftFinLE p ht).val ≠ k.val := by
      exact Nat.ne_of_lt (Nat.lt_of_lt_of_le p.isLt (Nat.succ_le_iff.mp hjk))
    have hp_row :
        (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE p ht] =
          b[GramSchmidt.liftFinLE p ht] :=
      rowAdd_row_eq_of_ne b j k (GramSchmidt.liftFinLE p ht) c hp_ne
    by_cases hqj : qf.val = j.val
    · have hqNat : q = j.val := by
        simpa [qf] using hqj
      have hq_last : qf = last := Fin.ext hqj
      simp only [GramSchmidt.scaledCoeffMatrix, Matrix.colReplace, Matrix.ofFn,
        Vector.getElem_ofFn, hqNat, if_true]
      rw [if_pos (rfl : (⟨j.val, Nat.lt_succ_self j.val⟩ : Fin t) = last)]
      simp only [Matrix.row]
      change Matrix.dot ((Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE p ht])
          ((Matrix.rowAdd b j k c)[k]) =
        oldCol p + c * gramCol p
      rw [hp_row]
      change Matrix.dot (b.row (GramSchmidt.liftFinLE p ht))
          ((Matrix.rowAdd b j k c)[k]) =
        oldCol p + c * gramCol p
      exact dot_rowAdd_row_at_right b j k c (b.row (GramSchmidt.liftFinLE p ht))
    · have hq_ne_last : qf ≠ last := by
        intro h
        exact hqj (congrArg Fin.val h)
      have hqNat : q ≠ j.val := by
        intro h
        exact hqj (by simpa [qf] using h)
      have hq_ne_k : (GramSchmidt.liftFinLE qf ht).val ≠ k.val := by
        exact Nat.ne_of_lt (Nat.lt_of_lt_of_le qf.isLt (Nat.succ_le_iff.mp hjk))
      have hq_row :
          (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE qf ht] =
            b[GramSchmidt.liftFinLE qf ht] :=
        rowAdd_row_eq_of_ne b j k (GramSchmidt.liftFinLE qf ht) c hq_ne_k
      simp only [GramSchmidt.scaledCoeffMatrix, Matrix.colReplace, Matrix.ofFn,
        Vector.getElem_ofFn, if_neg hqNat]
      rw [if_neg hq_ne_last]
      simp only [Matrix.row]
      rw [hp_row, hq_row]
      dsimp [M, GramSchmidt.leadingGramMatrixInt, Matrix.ofFn, Matrix.row]
      rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  have hold :
      GramSchmidt.scaledCoeffMatrix b k j hjk =
        Matrix.colReplace M last oldCol := by
    apply Vector.ext
    intro r hr
    apply Vector.ext
    intro q hq
    let p : Fin t := ⟨r, hr⟩
    let qf : Fin t := ⟨q, hq⟩
    by_cases hqj : qf.val = j.val
    · have hqNat : q = j.val := by
        simpa [qf] using hqj
      have hq_last : qf = last := Fin.ext hqj
      simp only [GramSchmidt.scaledCoeffMatrix, Matrix.colReplace, Matrix.ofFn,
        Vector.getElem_ofFn, hqNat, if_true]
      rw [if_pos (rfl : (⟨j.val, Nat.lt_succ_self j.val⟩ : Fin t) = last)]
    · have hq_ne_last : qf ≠ last := by
        intro h
        exact hqj (congrArg Fin.val h)
      have hqNat : q ≠ j.val := by
        intro h
        exact hqj (by simpa [qf] using h)
      simp only [GramSchmidt.scaledCoeffMatrix, Matrix.colReplace, Matrix.ofFn,
        Vector.getElem_ofFn, if_neg hqNat]
      rw [if_neg hq_ne_last]
      dsimp [M, GramSchmidt.leadingGramMatrixInt, Matrix.ofFn, Matrix.row]
      simp [Vector.getElem_ofFn]
  have hgram :
      Matrix.colReplace M last gramCol = M := by
    apply Vector.ext
    intro r hr
    apply Vector.ext
    intro q hq
    let p : Fin t := ⟨r, hr⟩
    let qf : Fin t := ⟨q, hq⟩
    by_cases hq_last : qf = last
    · have hq_lift : GramSchmidt.liftFinLE qf ht = j := by
        exact Fin.ext (by
          have hval := congrArg Fin.val hq_last
          simpa [last] using hval)
      simp only [M, gramCol, GramSchmidt.leadingGramMatrixInt, Matrix.colReplace, Matrix.ofFn,
        Vector.getElem_ofFn]
      rw [if_pos hq_last]
      rw [hq_lift]
    · simp only [M, gramCol, GramSchmidt.leadingGramMatrixInt, Matrix.colReplace, Matrix.ofFn,
        Vector.getElem_ofFn]
      rw [if_neg hq_last]
      simp [Matrix.row]
  calc
    Matrix.det (GramSchmidt.scaledCoeffMatrix (Matrix.rowAdd b j k c) k j hjk)
        = Matrix.det (Matrix.colReplace M last (fun p => oldCol p + c * gramCol p)) := by
          rw [hnew]
    _ = Matrix.det (Matrix.colReplace M last oldCol) +
          Matrix.det (Matrix.colReplace M last (fun p => c * gramCol p)) := by
          rw [Matrix.det_colReplace_add]
    _ = Matrix.det (Matrix.colReplace M last oldCol) +
          c * Matrix.det (Matrix.colReplace M last gramCol) := by
          rw [Matrix.det_colReplace_smul]
    _ = Matrix.det (GramSchmidt.scaledCoeffMatrix b k j hjk) +
          c * Matrix.det
            (GramSchmidt.leadingGramMatrixInt b (j.val + 1) (Nat.succ_le_of_lt j.isLt)) := by
          rw [← hold, hgram]

/-- The executable scaled-coefficient pivot entry changes predictably under
an earlier-row addition. This packages the Cramer/Bareiss pivot identity at
the public `scaledCoeffs` level so update consumers need not unfold the
determinant bridge directly. -/
theorem scaledCoeffs_rowAdd_pivot (b : Matrix Int n m) (j k : Fin n)
    (hjk : j.val < k.val) (c : Int) :
    GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k j =
      GramSchmidt.entry (scaledCoeffs b) k j +
        c * Int.ofNat (gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt)) := by
  have hnew := scaledCoeffs_eq_scaledCoeffMatrix_det
    (b := Matrix.rowAdd b j k c) (i := k) (j := j) hjk
  have hold := scaledCoeffs_eq_scaledCoeffMatrix_det (b := b) (i := k) (j := j) hjk
  have hbridge := scaledCoeffMatrix_rowAdd_pivot_det (b := b) (j := j) (k := k) hjk c
  have hlead := leadingGramMatrixInt_det_eq_gramDet_int
    (b := b) (t := j.val + 1) (ht := Nat.succ_le_of_lt j.isLt)
  calc
    GramSchmidt.entry (scaledCoeffs (Matrix.rowAdd b j k c)) k j =
        Matrix.det (GramSchmidt.scaledCoeffMatrix (Matrix.rowAdd b j k c) k j hjk) := hnew
    _ =
        Matrix.det (GramSchmidt.scaledCoeffMatrix b k j hjk) +
          c * Matrix.det
            (GramSchmidt.leadingGramMatrixInt b (j.val + 1)
              (Nat.succ_le_of_lt j.isLt)) := hbridge
    _ =
        GramSchmidt.entry (scaledCoeffs b) k j +
          c * Int.ofNat (gramDet b (j.val + 1) (Nat.succ_le_of_lt j.isLt)) := by
      rw [← hold, hlead]

/-- When the modified row index `k` lies outside the leading `t`-prefix
(`t ≤ k.val`), the leading Gram matrix of `Matrix.rowAdd b j k c` agrees with
that of `b`. -/
private theorem leadingGramMatrixInt_rowAdd_outside
    (b : Matrix Int n m) (j k : Fin n) (c : Int) (t : Nat) (ht : t ≤ n)
    (hkt : t ≤ k.val) :
    GramSchmidt.leadingGramMatrixInt (Matrix.rowAdd b j k c) t ht =
      GramSchmidt.leadingGramMatrixInt b t ht := by
  -- Prove the matrices agree row-by-row using a stronger row-level identity:
  -- for all r : Fin n with r.val < t, the rows of `rowAdd b j k c` and `b`
  -- agree.
  apply Vector.ext
  intro p hp
  apply Vector.ext
  intro q hq
  have hp_ne : (GramSchmidt.liftFinLE ⟨p, hp⟩ ht).val ≠ k.val :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le hp hkt)
  have hq_ne : (GramSchmidt.liftFinLE ⟨q, hq⟩ ht).val ≠ k.val :=
    Nat.ne_of_lt (Nat.lt_of_lt_of_le hq hkt)
  have hp_eq : (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE ⟨p, hp⟩ ht] =
      b[GramSchmidt.liftFinLE ⟨p, hp⟩ ht] :=
    rowAdd_row_eq_of_ne b j k (GramSchmidt.liftFinLE ⟨p, hp⟩ ht) c hp_ne
  have hq_eq : (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE ⟨q, hq⟩ ht] =
      b[GramSchmidt.liftFinLE ⟨q, hq⟩ ht] :=
    rowAdd_row_eq_of_ne b j k (GramSchmidt.liftFinLE ⟨q, hq⟩ ht) c hq_ne
  simp only [GramSchmidt.leadingGramMatrixInt, Matrix.ofFn, Matrix.row,
    Vector.getElem_ofFn, hp_eq, hq_eq]

/-- Entry-level structural identity for the leading Gram matrix of
`Matrix.rowAdd b j k c` when the modified row `k` lies inside the leading
`t`-prefix. The four cases (`p = k.val ∨ p ≠ k.val` × `q = k.val ∨ q ≠ k.val`)
are handled separately. -/
private theorem leadingGramMatrixInt_rowAdd_entry_inside
    (b : Matrix Int n m) (j k : Fin n) (c : Int) (t : Nat) (ht : t ≤ n)
    (hjk : j.val < k.val) (hkt : k.val < t)
    (p q : Fin t) :
    (GramSchmidt.leadingGramMatrixInt (Matrix.rowAdd b j k c) t ht)[p][q] =
      (Matrix.colAdd
          (Matrix.rowAdd (GramSchmidt.leadingGramMatrixInt b t ht)
            ⟨j.val, Nat.lt_trans hjk hkt⟩ ⟨k.val, hkt⟩ c)
          ⟨j.val, Nat.lt_trans hjk hkt⟩ ⟨k.val, hkt⟩ c)[p][q] := by
  -- Abbreviations as Fin t.
  let jt : Fin t := ⟨j.val, Nat.lt_trans hjk hkt⟩
  let kt : Fin t := ⟨k.val, hkt⟩
  -- liftFinLE jt ht = j, liftFinLE kt ht = k as Fin n.
  have hjt_lift : GramSchmidt.liftFinLE jt ht = j := Fin.ext rfl
  have hkt_lift : GramSchmidt.liftFinLE kt ht = k := Fin.ext rfl
  -- The Gram matrix entry as a dot product of integer rows.
  have hM_entry : ∀ (a b' : Fin t),
      (GramSchmidt.leadingGramMatrixInt b t ht)[a][b'] =
        Matrix.dot (b[GramSchmidt.liftFinLE a ht]) (b[GramSchmidt.liftFinLE b' ht]) := by
    intro a b'
    simp [GramSchmidt.leadingGramMatrixInt, Matrix.ofFn, Matrix.row,
      Vector.getElem_ofFn]
  -- LHS is a dot product over `Matrix.rowAdd b j k c` rows.
  have hLHS :
      (GramSchmidt.leadingGramMatrixInt (Matrix.rowAdd b j k c) t ht)[p][q] =
        Matrix.dot ((Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE p ht])
          ((Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE q ht]) := by
    simp [GramSchmidt.leadingGramMatrixInt, Matrix.ofFn, Matrix.row,
      Vector.getElem_ofFn]
  -- RHS: the colAdd-rowAdd entry as a conditional.
  have hRHS :
      (Matrix.colAdd
          (Matrix.rowAdd (GramSchmidt.leadingGramMatrixInt b t ht) jt kt c) jt kt c)[p][q] =
        if q = kt then
          (Matrix.rowAdd (GramSchmidt.leadingGramMatrixInt b t ht) jt kt c)[p][q] +
            c * (Matrix.rowAdd (GramSchmidt.leadingGramMatrixInt b t ht) jt kt c)[p][jt]
        else (Matrix.rowAdd (GramSchmidt.leadingGramMatrixInt b t ht) jt kt c)[p][q] := by
    simp [Matrix.colAdd, Matrix.ofFn, Vector.getElem_ofFn]
  rw [hLHS, hRHS]
  -- Case split on `q = kt` and `p = kt`.
  by_cases hqk : q = kt
  · -- q = kt branch
    rw [if_pos hqk]
    rw [rowAdd_get_rect (GramSchmidt.leadingGramMatrixInt b t ht) jt kt p c q,
        rowAdd_get_rect (GramSchmidt.leadingGramMatrixInt b t ht) jt kt p c jt]
    -- The `b[·]` rewrites for `liftFinLE jt ht` and `liftFinLE kt ht`
    -- give `b[j]` and `b[k]` respectively. These survive even when direct
    -- `rw` fails on motive: we rewrite the matrix row indexings via
    -- `congrArg b.get` once and reuse.
    have hbjt_lift : b[GramSchmidt.liftFinLE jt ht] = b[j] :=
      congrArg b.get hjt_lift
    have hbkt_lift : b[GramSchmidt.liftFinLE kt ht] = b[k] :=
      congrArg b.get hkt_lift
    by_cases hpk : p = kt
    · -- p = kt, q = kt
      have hpn_k : GramSchmidt.liftFinLE p ht = k :=
        Fin.ext (Fin.val_eq_of_eq hpk : p.val = kt.val)
      have hqn_k : GramSchmidt.liftFinLE q ht = k :=
        Fin.ext (Fin.val_eq_of_eq hqk : q.val = kt.val)
      have hrowAdd_p :
          (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE p ht] =
            (Matrix.rowAdd b j k c)[k] :=
        congrArg (Matrix.rowAdd b j k c).get hpn_k
      have hrowAdd_q :
          (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE q ht] =
            (Matrix.rowAdd b j k c)[k] :=
        congrArg (Matrix.rowAdd b j k c).get hqn_k
      rw [hrowAdd_p, hrowAdd_q]
      rw [dot_rowAdd_row_at_left b j k c ((Matrix.rowAdd b j k c)[k])]
      have hrec_k :
          Matrix.dot b[k] ((Matrix.rowAdd b j k c)[k]) =
            Matrix.dot b[k] b[k] + c * Matrix.dot b[k] b[j] :=
        dot_rowAdd_row_at_right b j k c b[k]
      have hrec_j :
          Matrix.dot b[j] ((Matrix.rowAdd b j k c)[k]) =
            Matrix.dot b[j] b[k] + c * Matrix.dot b[j] b[j] :=
        dot_rowAdd_row_at_right b j k c b[j]
      rw [hrec_k, hrec_j]
      simp only [if_pos hpk]
      rw [hM_entry kt q, hM_entry jt q, hM_entry kt jt, hM_entry jt jt]
      have hb_q : b[GramSchmidt.liftFinLE q ht] = b[k] :=
        congrArg b.get hqn_k
      rw [hbjt_lift, hbkt_lift, hb_q]
      have hsym : Matrix.dot b[j] b[k] = Matrix.dot b[k] b[j] := dot_comm_int _ _
      rw [hsym]
    · -- p ≠ kt, q = kt
      have hpn_ne : (GramSchmidt.liftFinLE p ht).val ≠ k.val :=
        fun h => hpk (Fin.ext h)
      have hqn_k : GramSchmidt.liftFinLE q ht = k :=
        Fin.ext (Fin.val_eq_of_eq hqk : q.val = kt.val)
      have hrowAdd_q :
          (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE q ht] =
            (Matrix.rowAdd b j k c)[k] :=
        congrArg (Matrix.rowAdd b j k c).get hqn_k
      have hb_q : b[GramSchmidt.liftFinLE q ht] = b[k] :=
        congrArg b.get hqn_k
      rw [hrowAdd_q]
      rw [rowAdd_row_eq_of_ne b j k (GramSchmidt.liftFinLE p ht) c hpn_ne]
      rw [dot_rowAdd_row_at_right b j k c (b[GramSchmidt.liftFinLE p ht])]
      simp only [if_neg hpk]
      rw [hM_entry p q, hM_entry p jt]
      rw [hbjt_lift, hb_q]
  · -- q ≠ kt branch
    rw [if_neg hqk]
    have hqn_ne : (GramSchmidt.liftFinLE q ht).val ≠ k.val :=
      fun h => hqk (Fin.ext h)
    rw [rowAdd_get_rect (GramSchmidt.leadingGramMatrixInt b t ht) jt kt p c q]
    rw [rowAdd_row_eq_of_ne b j k (GramSchmidt.liftFinLE q ht) c hqn_ne]
    have hbjt_lift : b[GramSchmidt.liftFinLE jt ht] = b[j] :=
      congrArg b.get hjt_lift
    have hbkt_lift : b[GramSchmidt.liftFinLE kt ht] = b[k] :=
      congrArg b.get hkt_lift
    by_cases hpk : p = kt
    · -- p = kt, q ≠ kt
      have hpn_k : GramSchmidt.liftFinLE p ht = k :=
        Fin.ext (Fin.val_eq_of_eq hpk : p.val = kt.val)
      have hrowAdd_p :
          (Matrix.rowAdd b j k c)[GramSchmidt.liftFinLE p ht] =
            (Matrix.rowAdd b j k c)[k] :=
        congrArg (Matrix.rowAdd b j k c).get hpn_k
      rw [hrowAdd_p]
      rw [dot_rowAdd_row_at_left b j k c (b[GramSchmidt.liftFinLE q ht])]
      simp only [if_pos hpk]
      rw [hM_entry kt q, hM_entry jt q]
      rw [hbjt_lift, hbkt_lift]
    · -- p ≠ kt, q ≠ kt
      have hpn_ne : (GramSchmidt.liftFinLE p ht).val ≠ k.val :=
        fun h => hpk (Fin.ext h)
      rw [rowAdd_row_eq_of_ne b j k (GramSchmidt.liftFinLE p ht) c hpn_ne]
      simp only [if_neg hpk]
      rw [hM_entry p q]

/-- When the modified row index `k` lies inside the leading `t`-prefix
(`k.val < t`), the leading Gram matrix of `Matrix.rowAdd b j k c` agrees with
the row-and-column-add of the original leading Gram matrix at the lifted
`Fin t` indices `jt`, `kt`. -/
private theorem leadingGramMatrixInt_rowAdd_inside
    (b : Matrix Int n m) (j k : Fin n) (c : Int) (t : Nat) (ht : t ≤ n)
    (hjk : j.val < k.val) (hkt : k.val < t) :
    GramSchmidt.leadingGramMatrixInt (Matrix.rowAdd b j k c) t ht =
      Matrix.colAdd
        (Matrix.rowAdd (GramSchmidt.leadingGramMatrixInt b t ht)
          ⟨j.val, Nat.lt_trans hjk hkt⟩ ⟨k.val, hkt⟩ c)
        ⟨j.val, Nat.lt_trans hjk hkt⟩ ⟨k.val, hkt⟩ c := by
  apply Vector.ext
  intro p hp
  apply Vector.ext
  intro q hq
  exact leadingGramMatrixInt_rowAdd_entry_inside b j k c t ht hjk hkt
    ⟨p, hp⟩ ⟨q, hq⟩

/-- Adding a multiple of an earlier row to a later row leaves the leading
Gram determinant unchanged. The hypothesis `j.val < k.val` makes the source
row earlier than the destination row in the basis. -/
theorem gramDet_rowAdd_earlier
    (b : Matrix Int n m) (j k : Fin n) (c : Int) (t : Nat) (ht : t ≤ n)
    (hjk : j.val < k.val) :
    gramDet (Matrix.rowAdd b j k c) t ht = gramDet b t ht := by
  unfold gramDet
  -- Reduce to the underlying Bareiss-determinant equality on `Int`.
  congr 1
  by_cases hkt : k.val < t
  · -- Inside case: bareiss = det, then det_rowAdd / det_colAdd preserve.
    rw [leadingGramMatrixInt_rowAdd_inside b j k c t ht hjk hkt]
    rw [Matrix.bareiss_eq_det, Matrix.bareiss_eq_det]
    -- Indices and inequality between `jt` and `kt` in `Fin t`.
    have hjt_ne_kt : (⟨j.val, Nat.lt_trans hjk hkt⟩ : Fin t) ≠ ⟨k.val, hkt⟩ := by
      intro h
      have hval : (⟨j.val, Nat.lt_trans hjk hkt⟩ : Fin t).val =
          (⟨k.val, hkt⟩ : Fin t).val :=
        congrArg Fin.val h
      exact Nat.ne_of_lt hjk hval
    rw [Matrix.det_colAdd _ _ _ _ hjt_ne_kt]
    rw [Matrix.det_rowAdd _ _ _ _ hjt_ne_kt]
  · -- Outside case: leading prefix unchanged.
    have hkt' : t ≤ k.val := Nat.le_of_not_lt hkt
    rw [leadingGramMatrixInt_rowAdd_outside b j k c t ht hkt']

/-! ### Adjacent-swap pivot Gram-determinant product

Swapping adjacent rows `km1, k` (with `km1 + 1 = k`) of `b` changes only the
leading `k × k` Gram determinant within `0 ≤ t ≤ k + 1`. The new pivot Gram
determinant `gramDet (rowSwap b km1 k) k` satisfies the integer product
identity

    gramDet b' k · gramDet b k = gramDet b (k+1) · gramDet b km1 + B²

where `B = (scaledCoeffs b)[k][km1]`. This is the fraction-free form of the
standard rational adjacent-swap update used by integer LLL. -/

/-- If two integers cast to equal rationals, they are equal. -/
private theorem intCast_rat_injective_int_eq {a b : Int} (h : (a : Rat) = (b : Rat)) :
    a = b := by
  have hz : ((a - b : Int) : Rat) = 0 := by
    push_cast
    grind
  have hsub : a - b = 0 := Rat.intCast_eq_zero_iff.mp hz
  omega

private theorem dot_add_left_rat {m' : Nat} (u v w : Vector Rat m') :
    Matrix.dot (u + v) w = Matrix.dot u w + Matrix.dot v w := by
  rw [dot_comm_rat (u := u + v) (v := w)]
  rw [dot_add_right_rat (u := w) (v := u) (w := v)]
  rw [dot_comm_rat (u := w) (v := u), dot_comm_rat (u := w) (v := v)]

private theorem dot_smul_left_rat {m' : Nat} (s : Rat) (u v : Vector Rat m') :
    Matrix.dot (s • u) v = s * Matrix.dot u v := by
  rw [dot_comm_rat (u := s • u) (v := v)]
  rw [dot_smul_right_rat (s := s) (u := v) (v := u)]
  rw [dot_comm_rat (u := v) (v := u)]

/-- Pythagoras: if `curr ⊥ prev`, then the squared norm of `curr + μ • prev`
splits as `‖curr‖² + μ² · ‖prev‖²`. -/
private theorem normSq_add_smul_orthogonal_rat {m' : Nat}
    (curr prev : Vector Rat m') (μ : Rat)
    (horth : Matrix.dot curr prev = 0) :
    Vector.normSq (curr + μ • prev) =
      Vector.normSq curr + μ ^ 2 * Vector.normSq prev := by
  show Matrix.dot (curr + μ • prev) (curr + μ • prev) =
    Matrix.dot curr curr + μ ^ 2 * Matrix.dot prev prev
  rw [dot_add_left_rat (u := curr) (v := μ • prev) (w := curr + μ • prev)]
  rw [dot_add_right_rat (u := curr) (v := curr) (w := μ • prev)]
  rw [dot_add_right_rat (u := μ • prev) (v := curr) (w := μ • prev)]
  rw [dot_smul_right_rat (s := μ) (u := curr) (v := prev)]
  rw [dot_smul_left_rat (s := μ) (u := prev) (v := curr)]
  rw [dot_smul_left_rat (s := μ) (u := prev) (v := μ • prev)]
  rw [dot_smul_right_rat (s := μ) (u := prev) (v := prev)]
  have horth_swap : Matrix.dot prev curr = 0 := by
    rw [dot_comm_rat]; exact horth
  rw [horth, horth_swap]
  grind

/-- For `j < km1.val`, the Gram-Schmidt basis row is unchanged by the swap
of rows `km1, k`. The norm-square product over indices `< km1.val` therefore
agrees on `b` and `Matrix.rowSwap b km1 k`. -/
private theorem gramSchmidtNormProduct_rowSwap_below
    (b : Matrix Int n m) (km1 k : Fin n) (hkm1k : km1.val < k.val) :
    gramSchmidtNormProduct (Matrix.rowSwap b km1 k) km1.val
        (Nat.le_of_lt km1.isLt) =
      gramSchmidtNormProduct b km1.val (Nat.le_of_lt km1.isLt) := by
  unfold gramSchmidtNormProduct
  apply foldl_mul_congr_simple
  intro j _hj
  have hj_lt_km1 : j.val < km1.val := j.isLt
  congr 1
  exact basis_rowSwap_of_before b km1 k
    ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_of_lt km1.isLt)⟩ hkm1k hj_lt_km1

/-- Unconditional version of `gramDet_eq_prod_normSq`: the leading Gram
determinant casts to the rational `gramSchmidtNormProduct` without requiring
linear independence. The `independent` hypothesis in the public theorem is
not actually used by the proof. -/
private theorem gramDet_eq_prod_normSq_uncond (b : Matrix Int n m)
    (k : Nat) (hk : k ≤ n) :
    (gramDet b k hk : Rat) = gramSchmidtNormProduct b k hk := by
  rw [gramDet_rat_eq_progressMatrix_zero_det b k hk]
  rw [← progressMatrix_det_invariant b k hk k (Nat.le_refl k)]
  rw [progressMatrix_full_eq_auxMatrix]
  exact auxMatrix_det_eq_prod_normSq b k hk

/-- `gramDet` is independent of the propositional `≤ n` proof, and depends only
on the Nat value `k`. Two `gramDet` calls with equal `Nat` arguments produce
equal values. -/
private theorem gramDet_subst_val
    (b : Matrix Int n m) (j₁ j₂ : Nat) (h₁ : j₁ ≤ n) (h₂ : j₂ ≤ n)
    (he : j₁ = j₂) :
    gramDet b j₁ h₁ = gramDet b j₂ h₂ := by
  subst he
  rfl

/-- Same as `gramDet_subst_val` for `gramSchmidtNormProduct`. -/
private theorem gramSchmidtNormProduct_subst_val
    (b : Matrix Int n m) (j₁ j₂ : Nat) (h₁ : j₁ ≤ n) (h₂ : j₂ ≤ n)
    (he : j₁ = j₂) :
    gramSchmidtNormProduct b j₁ h₁ = gramSchmidtNormProduct b j₂ h₂ := by
  subst he
  rfl

/-- Integer fraction-free identity for the leading pivot Gram determinant
after swapping adjacent rows `km1, k` with `km1.val + 1 = k.val`:

    gramDet b' k · gramDet b k = gramDet b (k+1) · gramDet b km1 + B²

where `B = (scaledCoeffs b)[k][km1]`. This is the algebraic heart of the
integer LLL adjacent-swap update. -/
theorem gramDet_rowSwap_adjacent_pivot_product
    (b : Matrix Int n m) (km1 k : Fin n) (hkm1 : km1.val + 1 = k.val) :
    let B : Int := GramSchmidt.entry (scaledCoeffs b) k km1
    ((gramDet (Matrix.rowSwap b km1 k) k.val (Nat.le_of_lt k.isLt) : Nat) : Int) *
        ((gramDet b k.val (Nat.le_of_lt k.isLt) : Nat) : Int) =
      ((gramDet b (k.val + 1) (Nat.succ_le_of_lt k.isLt) : Nat) : Int) *
          ((gramDet b km1.val (Nat.le_of_lt km1.isLt) : Nat) : Int) +
        B ^ 2 := by
  intro B
  have hkm1k : km1.val < k.val := by omega
  have hkm1_le_n : km1.val ≤ n := Nat.le_of_lt km1.isLt
  have hk_le_n : k.val ≤ n := Nat.le_of_lt k.isLt
  have hk1_le_n : k.val + 1 ≤ n := Nat.succ_le_of_lt k.isLt
  have hkm1_succ_le : km1.val + 1 ≤ n := Nat.succ_le_of_lt km1.isLt
  -- Local abbreviations on the rational side.
  let μ : Rat := GramSchmidt.entry (coeffs b) k km1
  let prev : Vector Rat m := (basis b).row km1
  let curr : Vector Rat m := (basis b).row k
  let G : Rat := gramSchmidtNormProduct b km1.val hkm1_le_n
  let Nkm1 : Rat := Vector.normSq prev
  let Nk : Rat := Vector.normSq curr
  -- Rational expressions for each Gram determinant we touch.
  have hdkm1_rat : (gramDet b km1.val hkm1_le_n : Rat) = G :=
    gramDet_eq_prod_normSq_uncond b km1.val hkm1_le_n
  -- gramDet b k.val = gramDet b (km1.val + 1) = G * Nkm1.
  have hdk_rat : (gramDet b k.val hk_le_n : Rat) = G * Nkm1 := by
    have h_succ := gramDet_succ_rat b km1.val hkm1_succ_le
    have hgd_eq :
        gramDet b (km1.val + 1) hkm1_succ_le = gramDet b k.val hk_le_n :=
      gramDet_subst_val b _ _ _ _ hkm1
    rw [← hgd_eq, h_succ]
  -- gramDet b (k.val + 1) = G * Nkm1 * Nk.
  have hdkp1_rat : (gramDet b (k.val + 1) hk1_le_n : Rat) = G * Nkm1 * Nk := by
    have h_succ := gramDet_succ_rat b k.val hk1_le_n
    have hgnp_k_eq :
        gramSchmidtNormProduct b k.val hk_le_n =
          gramSchmidtNormProduct b (km1.val + 1) hkm1_succ_le :=
      gramSchmidtNormProduct_subst_val b _ _ _ _ hkm1.symm
    rw [h_succ, hgnp_k_eq,
        gramSchmidtNormProduct_succ b km1.val hkm1_succ_le]
  -- Basis orthogonality between curr and prev.
  have horth : Matrix.dot curr prev = 0 :=
    basis_orthogonal b k.val km1.val k.isLt km1.isLt (by omega)
  -- New basis row at km1 of the swapped matrix is `curr + μ • prev`.
  have hbasis_swap :
      (basis (Matrix.rowSwap b km1 k)).row km1 = curr + μ • prev :=
    basis_rowSwap_adjacent_prev b km1 k hkm1
  -- gramDet (rowSwap b km1 k) k.val = G * (Nk + μ^2 * Nkm1).
  have hdprime_rat :
      (gramDet (Matrix.rowSwap b km1 k) k.val hk_le_n : Rat) =
        G * (Nk + μ ^ 2 * Nkm1) := by
    have h_succ :=
      gramDet_succ_rat (Matrix.rowSwap b km1 k) km1.val hkm1_succ_le
    have hgd_eq :
        gramDet (Matrix.rowSwap b km1 k) (km1.val + 1) hkm1_succ_le =
          gramDet (Matrix.rowSwap b km1 k) k.val hk_le_n :=
      gramDet_subst_val (Matrix.rowSwap b km1 k) _ _ _ _ hkm1
    rw [← hgd_eq, h_succ,
        gramSchmidtNormProduct_rowSwap_below b km1 k hkm1k]
    show G * Vector.normSq ((basis (Matrix.rowSwap b km1 k)).row
        ⟨km1.val, km1.isLt⟩) = G * (Nk + μ ^ 2 * Nkm1)
    have hbasis_row :
        (basis (Matrix.rowSwap b km1 k)).row ⟨km1.val, km1.isLt⟩ =
          curr + μ • prev := hbasis_swap
    rw [hbasis_row, normSq_add_smul_orthogonal_rat curr prev μ horth]
  -- Rational expression for B.
  have hB_rat : ((B : Int) : Rat) = G * Nkm1 * μ := by
    show ((GramSchmidt.entry (scaledCoeffs b) k km1 : Int) : Rat) =
        G * Nkm1 * μ
    rw [scaledCoeffs_eq b k.val km1.val k.isLt hkm1k]
    have hgd_eq :
        gramDet b (km1.val + 1)
            (Nat.succ_le_of_lt (Nat.lt_trans hkm1k k.isLt)) =
          gramDet b k.val hk_le_n :=
      gramDet_subst_val b _ _ _ _ hkm1
    show (gramDet b (km1.val + 1) _ : Rat) *
        GramSchmidt.entry (coeffs b) ⟨k.val, k.isLt⟩
          ⟨km1.val, Nat.lt_trans hkm1k k.isLt⟩ = G * Nkm1 * μ
    rw [hgd_eq, hdk_rat]
  -- Promote to Rat and discharge.
  apply intCast_rat_injective_int_eq
  push_cast
  rw [hdprime_rat, hdk_rat, hdkp1_rat, hdkm1_rat, hB_rat]
  grind

end GramSchmidt.Int

namespace GramSchmidt.Rat

/-- The `k`-th Gram determinant for a rational input matrix. -/
def gramDet (b : Matrix Rat n m) (k : Nat) (hk : k ≤ n) : Rat :=
  Matrix.det (GramSchmidt.leadingGramMatrixRat b k hk)

end GramSchmidt.Rat

end Hex
