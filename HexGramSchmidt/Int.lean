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

/-- Linear independence of the row prefix determinants used by the
Gram-Schmidt theorem surface. -/
def independent (b : Matrix Int n m) : Prop :=
  ∀ k : Fin n, 0 < Matrix.det (Matrix.submatrix (Matrix.gramMatrix b) k)

/-- The `k`-th Gram determinant: the determinant of the `k × k` leading
principal Gram matrix of the integer input. -/
def gramDet (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) : Nat :=
  (Matrix.bareiss (GramSchmidt.leadingGramMatrixInt b k hk)).toNat

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

/-- All leading Gram determinants, starting with the empty-prefix value
`d₀ = 1`. -/
def gramDetVec (b : Matrix Int n m) : Vector Nat (n + 1) :=
  let gram := Matrix.gramMatrix b
  let data := Matrix.bareissNoPivotData gram
  Vector.ofFn fun k => gramDetVecEntry data k

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
def scaledCoeffs (b : Matrix Int n m) : Matrix Int n n :=
  rowsToMatrix (scaledCoeffRows b) n

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
  sorry

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
  simpa [gramDetVec] using gramDetVecEntry_eq_gramDet (b := b) k hk

theorem gramDet_eq_prod_normSq (b : Matrix Int n m)
    (hli : independent b) (k : Nat) (hk : k ≤ n) :
    (gramDet b k hk : Rat) = gramSchmidtNormProduct b k hk := by
  sorry

theorem gramDet_pos (b : Matrix Int n m)
    (hli : independent b) (k : Nat) (hk : k ≤ n) (hk' : 0 < k) :
    0 < gramDet b k hk := by
  sorry

theorem basis_normSq (b : Matrix Int n m)
    (hli : independent b) (k : Nat) (hk : k < n) :
    Vector.normSq ((basis b).row ⟨k, hk⟩) =
      (gramDet b (k + 1) (Nat.succ_le_of_lt hk) : Rat) /
        (gramDet b k (Nat.le_of_lt hk) : Rat) := by
  sorry

theorem scaledCoeffs_eq (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < i) :
    ((GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ : Int) : Rat) =
      (gramDet b (j + 1) (Nat.succ_le_of_lt (Nat.lt_trans hj hi)) : Rat) *
        GramSchmidt.entry (coeffs b) ⟨i, hi⟩ ⟨j, Nat.lt_trans hj hi⟩ := by
  simpa [scaledCoeffs, rowsToMatrix, GramSchmidt.entry, Matrix.row, Matrix.ofFn] using
    scaledCoeffRows_lower_eq_coeffs (b := b) i j hi hj

theorem scaledCoeffs_diag (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨i, hi⟩ =
      Int.ofNat (gramDet b (i + 1) (Nat.succ_le_of_lt hi)) := by
  simpa [scaledCoeffs, rowsToMatrix, GramSchmidt.entry, Matrix.row, Matrix.ofFn] using
    scaledCoeffRows_diag_eq_gramDet (b := b) i hi

theorem scaledCoeffs_upper (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i < j) :
    GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨j, hj⟩ = 0 := by
  simpa [scaledCoeffs, rowsToMatrix, scaledCoeffRows, GramSchmidt.entry, Matrix.row,
    Matrix.ofFn] using getArrayEntry_scaledCoeffArrayLoop_above n n
    { step := 0
      matrix := gramRows b
      coeffs := zeroRows n
      prevPivot := 1 }
    (by
      intro r c hrc
      exact getArrayEntry_zeroRows n r c)
    i j hij

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

end GramSchmidt.Int

namespace GramSchmidt.Rat

/-- The `k`-th Gram determinant for a rational input matrix. -/
def gramDet (b : Matrix Rat n m) (k : Nat) (hk : k ≤ n) : Rat :=
  Matrix.det (GramSchmidt.leadingGramMatrixRat b k hk)

end GramSchmidt.Rat

end Hex
