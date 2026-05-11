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

private theorem gramDet_pos_core (b : Matrix Int n m)
    (hli : independent b) (k : Nat) (hk : k ≤ n) (hk' : 0 < k) :
    0 < gramDet b k hk := by
  cases k with
  | zero =>
      omega
  | succ r =>
      have hrn : r < n := Nat.lt_of_succ_le hk
      let last : Fin n := ⟨r, hrn⟩
      have hsub : 0 < Matrix.det (Matrix.submatrix (Matrix.gramMatrix b) last) :=
        hli last
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

private theorem basis_normSq_core (b : Matrix Int n m)
    (hli : independent b) (k : Nat) (hk : k < n) :
    Vector.normSq ((basis b).row ⟨k, hk⟩) =
      (gramDet b (k + 1) (Nat.succ_le_of_lt hk) : Rat) /
        (gramDet b k (Nat.le_of_lt hk) : Rat) := by
  sorry

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
    (b : Matrix Rat n m) (i : Nat) (hi : i < n) (u : Vector Rat m) :
    Matrix.dot u
        (GramSchmidt.prefixCombination
          (GramSchmidt.Rat.coeffs b) (GramSchmidt.Rat.basis b) i hi) =
      (List.finRange i).foldl
        (fun (acc : Rat) (j : Fin i) =>
          acc +
            GramSchmidt.entry (GramSchmidt.Rat.coeffs b) ⟨i, hi⟩
                ⟨j.val, Nat.lt_trans j.isLt hi⟩ *
              Matrix.dot u
                ((GramSchmidt.Rat.basis b).row
                  ⟨j.val, Nat.lt_trans j.isLt hi⟩)) 0 := by
  unfold GramSchmidt.prefixCombination
  have hgen :
      ∀ (xs : List (Fin i)) (acc : Vector Rat m),
        Matrix.dot u
            (xs.foldl
              (fun acc (j : Fin i) =>
                acc +
                  GramSchmidt.entry (GramSchmidt.Rat.coeffs b) ⟨i, hi⟩
                      ⟨j.val, Nat.lt_trans j.isLt hi⟩ •
                    (GramSchmidt.Rat.basis b).row
                      ⟨j.val, Nat.lt_trans j.isLt hi⟩)
              acc) =
          Matrix.dot u acc +
            xs.foldl
              (fun (acc' : Rat) (j : Fin i) =>
                acc' +
                  GramSchmidt.entry (GramSchmidt.Rat.coeffs b) ⟨i, hi⟩
                      ⟨j.val, Nat.lt_trans j.isLt hi⟩ *
                    Matrix.dot u
                      ((GramSchmidt.Rat.basis b).row
                        ⟨j.val, Nat.lt_trans j.isLt hi⟩)) 0 := by
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
          ((0 : Rat) + (GramSchmidt.entry (GramSchmidt.Rat.coeffs b) ⟨i, hi⟩
              ⟨x.val, Nat.lt_trans x.isLt hi⟩ *
            Matrix.dot u
              ((GramSchmidt.Rat.basis b).row
                ⟨x.val, Nat.lt_trans x.isLt hi⟩)))]
        grind
  rw [hgen (List.finRange i) 0]
  rw [dot_zero_right_rat]
  grind

/-- Dot product against a `prefixCombination` is zero when the right vector is
orthogonal to every contributing basis row. -/
private theorem dot_prefixCombination_right_eq_zero_of_dot_zero
    (b : Matrix Rat n m) (i : Nat) (hi : i < n) (u : Vector Rat m)
    (h : ∀ (j : Fin i),
      Matrix.dot u
          ((GramSchmidt.Rat.basis b).row ⟨j.val, Nat.lt_trans j.isLt hi⟩) = 0) :
    Matrix.dot u
        (GramSchmidt.prefixCombination
          (GramSchmidt.Rat.coeffs b) (GramSchmidt.Rat.basis b) i hi) = 0 := by
  rw [dot_prefixCombination_right_rat]
  -- All terms are zero: the foldl with each entry = 0 reduces to 0.
  induction (List.finRange i) with
  | nil => rfl
  | cons j xs ih =>
      simp only [List.foldl_cons]
      rw [h j]
      have h0 : (0 : Rat) + GramSchmidt.entry (GramSchmidt.Rat.coeffs b) ⟨i, hi⟩
          ⟨j.val, Nat.lt_trans j.isLt hi⟩ * 0 = 0 := by grind
      rw [h0]
      exact ih

theorem gramDet_eq_prod_normSq (b : Matrix Int n m)
    (hli : independent b) (k : Nat) (hk : k ≤ n) :
    (gramDet b k hk : Rat) = gramSchmidtNormProduct b k hk := by
  sorry

theorem gramDet_pos (b : Matrix Int n m)
    (hli : independent b) (k : Nat) (hk : k ≤ n) (hk' : 0 < k) :
    0 < gramDet b k hk := by
  exact gramDet_pos_core b hli k hk hk'

theorem basis_normSq (b : Matrix Int n m)
    (hli : independent b) (k : Nat) (hk : k < n) :
    Vector.normSq ((basis b).row ⟨k, hk⟩) =
      (gramDet b (k + 1) (Nat.succ_le_of_lt hk) : Rat) /
        (gramDet b k (Nat.le_of_lt hk) : Rat) := by
  exact basis_normSq_core b hli k hk

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

end GramSchmidt.Int

namespace GramSchmidt.Rat

/-- The `k`-th Gram determinant for a rational input matrix. -/
def gramDet (b : Matrix Rat n m) (k : Nat) (hk : k ≤ n) : Rat :=
  Matrix.det (GramSchmidt.leadingGramMatrixRat b k hk)

end GramSchmidt.Rat

end Hex
