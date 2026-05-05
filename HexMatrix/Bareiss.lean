import HexMatrix.Determinant

/-!
Executable Bareiss determinant algorithm for `hex-matrix`.

This module implements fraction-free Bareiss elimination over `Int` in two
layers: a no-pivot recurrence that follows the standard exact-division update,
and a public row-pivoting wrapper that swaps in a nonzero pivot when needed and
tracks the resulting determinant sign. The root library also exposes the
theorem surface relating this executable path to the generic determinant.
-/

namespace Hex

universe u

namespace Matrix

variable {n : Nat}

/-- Output of an executable Bareiss elimination pass. -/
structure BareissData (n : Nat) where
  matrix : Matrix Int n n
  rowSwaps : Nat
  singularStep : Option Nat

namespace BareissData

/-- The determinant sign contributed by the recorded row swaps. -/
def sign (data : BareissData n) : Int :=
  if data.rowSwaps % 2 = 0 then 1 else -1

private def lastDiag? (M : Matrix Int n n) : Option Int :=
  match n with
  | 0 => none
  | k + 1 =>
      let i : Fin (k + 1) := ⟨k, Nat.lt_succ_self k⟩
      some M[i][i]

/-- The determinant encoded by a Bareiss elimination result. -/
def det (data : BareissData n) : Int :=
  match data.singularStep with
  | some _ => 0
  | none =>
      match lastDiag? data.matrix with
      | some d => data.sign * d
      | none => data.sign

end BareissData

/-- Internal state of the no-pivot Bareiss recurrence, exposed read-only for
the Mathlib-side determinant proof. -/
structure BareissState (n : Nat) where
  step : Nat
  matrix : Matrix Int n n
  prevPivot : Int
  rowSwaps : Nat
  singularStep : Option Nat

/-- Exact division used by the Bareiss recurrence. The `else` branch is
defensive; for matrices produced by the Bareiss update, divisibility should
always hold. -/
def exactDiv (num denom : Int) : Int :=
  if h : denom ∣ num then
    Int.divExact num denom h
  else
    0

/-- When divisibility is known, `exactDiv` is the GMP-backed exact quotient. -/
theorem exactDiv_eq_divExact {num denom : Int} (h : denom ∣ num) :
    exactDiv num denom = Int.divExact num denom h := by
  simp [exactDiv, h]

/-- Search column `col` for a nonzero pivot at or below `start`. -/
private def findPivotAux (M : Matrix Int n n) (col : Fin n) (start fuel : Nat) :
    Option (Fin n) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if h : start < n then
        let i : Fin n := ⟨start, h⟩
        if M[i][col] = 0 then
          findPivotAux M col (start + 1) fuel
        else
          some i
      else
        none

/-- Search column `col` for a nonzero pivot at or below `start`. -/
private def findPivot? (M : Matrix Int n n) (col : Fin n) (start : Nat) :
    Option (Fin n) :=
  findPivotAux M col start (n - start)

/-- Apply one Bareiss update step to the trailing submatrix strictly below and
to the right of the current pivot. -/
def stepMatrix (M : Matrix Int n n) (k : Nat) (pivot prevPivot : Int) :
    Matrix Int n n :=
  Matrix.ofFn fun i j =>
    if hkij : k < i.val ∧ k < j.val then
      let colK : Fin n := ⟨k, Nat.lt_trans hkij.1 i.isLt⟩
      let rowK : Fin n := ⟨k, Nat.lt_trans hkij.2 j.isLt⟩
      exactDiv (pivot * M[i][j] - M[i][colK] * M[rowK][j]) prevPivot
    else if hBelow : k < i.val ∧ j.val = k then
      0
    else
      M[i][j]

/-- Outside the trailing update region and pivot column below the pivot,
`stepMatrix` leaves entries unchanged. -/
theorem stepMatrix_eq_of_not_update
    (M : Matrix Int n n) (k : Nat) (pivot prevPivot : Int) (i j : Fin n)
    (htrail : ¬ (k < i.val ∧ k < j.val))
    (hcol : ¬ (k < i.val ∧ j.val = k)) :
    (stepMatrix M k pivot prevPivot)[i][j] = M[i][j] := by
  simp [stepMatrix, Matrix.ofFn, htrail, hcol]

/-- `stepMatrix` preserves diagonal entries whose index is at or before the
current pivot step. -/
theorem stepMatrix_diag_of_le
    (M : Matrix Int n n) (k : Nat) (pivot prevPivot : Int) (i : Fin n)
    (hi : i.val ≤ k) :
    (stepMatrix M k pivot prevPivot)[i][i] = M[i][i] := by
  apply stepMatrix_eq_of_not_update
  · intro htrail
    exact Nat.not_lt_of_ge hi htrail.1
  · intro hcol
    exact Nat.not_lt_of_ge hi hcol.1

/-- `stepMatrix` clears the pivot column below the current pivot. -/
theorem stepMatrix_pivot_col_below
    (M : Matrix Int n n) (k : Nat) (pivot prevPivot : Int) (i colK : Fin n)
    (hi : k < i.val) (hcolK : colK.val = k) :
    (stepMatrix M k pivot prevPivot)[i][colK] = 0 := by
  simp [stepMatrix, Matrix.ofFn, hi, hcolK]

/-- Entry formula for the trailing block updated by one Bareiss step. -/
theorem stepMatrix_update_eq
    (M : Matrix Int n n) (k : Nat) (pivot prevPivot : Int) (i j : Fin n)
    (hi : k < i.val) (hj : k < j.val) :
    (stepMatrix M k pivot prevPivot)[i][j] =
      (let colK : Fin n := ⟨k, Nat.lt_trans hi i.isLt⟩
       let rowK : Fin n := ⟨k, Nat.lt_trans hj j.isLt⟩
       exactDiv (pivot * M[i][j] - M[i][colK] * M[rowK][j]) prevPivot) := by
  simp [stepMatrix, Matrix.ofFn, hi, hj]

/-- If the current matrix entries already match bordered minors and exact
division evaluates to the next bordered minor, then one `stepMatrix` update
preserves the bordered-minor invariant at the updated entry. -/
theorem stepMatrix_borderedMinor_update
    (source current : Matrix Int n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) (hi : k < i.val) (hj : k < j.val) (pivot prevPivot : Int)
    (hpivot :
      pivot =
        det (borderedMinor source k hk
          (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
          (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)))
    (hentry :
      current[i][j] = det (borderedMinor source k hk i j))
    (hleft :
      current[i][(⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)] =
        det (borderedMinor source k hk i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)))
    (htop :
      current[(⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)][j] =
        det (borderedMinor source k hk (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j))
    (hexact :
      exactDiv
        (det (borderedMinor source k hk
            (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)
            (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          det (borderedMinor source k hk i j) -
          det (borderedMinor source k hk i (⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)) *
          det (borderedMinor source k hk (⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n) j))
        prevPivot =
          det (borderedMinor source (k + 1) hnext i j)) :
    (stepMatrix current k pivot prevPivot)[i][j] =
      det (borderedMinor source (k + 1) hnext i j) := by
  rw [stepMatrix_update_eq current k pivot prevPivot i j hi hj]
  change
    exactDiv
      (pivot * current[i][j] -
        current[i][(⟨k, Nat.lt_trans hi i.isLt⟩ : Fin n)] *
        current[(⟨k, Nat.lt_trans hj j.isLt⟩ : Fin n)][j])
      prevPivot =
        det (borderedMinor source (k + 1) hnext i j)
  rw [hpivot, hentry, hleft, htop]
  exact hexact

private structure BareissArrayState where
  step : Nat
  matrix : Array (Array Int)
  prevPivot : Int
  rowSwaps : Nat
  singularStep : Option Nat

@[inline] private def getEntry (rows : Array (Array Int)) (row col : Nat) : Int :=
  rows[row]![col]!

private def matrixToRows (M : Matrix Int n n) : Array (Array Int) :=
  (Array.range n).map fun row =>
    (Array.range n).map fun col =>
      if hrow : row < n then
        if hcol : col < n then
          let i : Fin n := ⟨row, hrow⟩
          let j : Fin n := ⟨col, hcol⟩
          M[i][j]
        else
          0
      else
        0

private def rowsToMatrix (rows : Array (Array Int)) (n : Nat) : Matrix Int n n :=
  Matrix.ofFn fun i j => getEntry rows i.val j.val

private def swapRowsArray (rows : Array (Array Int)) (rowA rowB : Nat) :
    Array (Array Int) :=
  if rowA = rowB then
    rows
  else
    (rows.set! rowA rows[rowB]!).set! rowB rows[rowA]!

private def findPivotArrayAux
    (rows : Array (Array Int)) (n col start fuel : Nat) : Option Nat :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
      if start < n then
        if getEntry rows start col = 0 then
          findPivotArrayAux rows n col (start + 1) fuel
        else
          some start
      else
        none

private def findPivotArray? (rows : Array (Array Int)) (n col start : Nat) :
    Option Nat :=
  findPivotArrayAux rows n col start (n - start)

private def stepArray (rows : Array (Array Int)) (n k : Nat) (pivot prevPivot : Int) :
    Array (Array Int) :=
  Id.run do
    let mut next := rows
    for i in [k + 1:n] do
      let sourceRow := rows[i]!
      let entryIK := sourceRow[k]!
      let mut nextRow := sourceRow.set! k 0
      for j in [k + 1:n] do
        let value :=
          (pivot * sourceRow[j]! - entryIK * getEntry rows k j) / prevPivot
        nextRow := nextRow.set! j value
      next := next.set! i nextRow
    return next

private def pivotArrayLoop (n fuel : Nat) (state : BareissArrayState) :
    BareissArrayState :=
  match fuel with
  | 0 => state
  | fuel + 1 =>
      if state.step + 1 < n then
        let k := state.step
        let (rows, swaps) :=
          if getEntry state.matrix k k = 0 then
            match findPivotArray? state.matrix n k (state.step + 1) with
            | some pivot => (swapRowsArray state.matrix k pivot, state.rowSwaps + 1)
            | none => (state.matrix, state.rowSwaps)
          else
            (state.matrix, state.rowSwaps)
        let pivot := getEntry rows k k
        if pivot = 0 then
          { state with matrix := rows, rowSwaps := swaps, singularStep := some state.step }
        else
          let next : BareissArrayState :=
            { step := state.step + 1
              matrix := stepArray rows n state.step pivot state.prevPivot
              prevPivot := pivot
              rowSwaps := swaps
              singularStep := none }
          pivotArrayLoop n fuel next
      else
        state

private def bareissArrayState (M : Matrix Int n n) : BareissArrayState :=
  pivotArrayLoop n n
    { step := 0
      matrix := matrixToRows M
      prevPivot := 1
      rowSwaps := 0
      singularStep := none }

private def arraySign (rowSwaps : Nat) : Int :=
  if rowSwaps % 2 = 0 then 1 else -1

private def arrayLastDiag? (rows : Array (Array Int)) (n : Nat) : Option Int :=
  match n with
  | 0 => none
  | k + 1 => some (getEntry rows k k)

private def bareissArrayDet (state : BareissArrayState) (n : Nat) : Int :=
  match state.singularStep with
  | some _ => 0
  | none =>
      match arrayLastDiag? state.matrix n with
      | some d => arraySign state.rowSwaps * d
      | none => arraySign state.rowSwaps

/-- Package a Bareiss state as public elimination data. -/
def finish (state : BareissState n) : BareissData n :=
  { matrix := state.matrix
    rowSwaps := state.rowSwaps
    singularStep := state.singularStep }

/-- Bareiss elimination without pivoting. A zero pivot aborts and records the
singular step. -/
def noPivotLoop (fuel : Nat) (state : BareissState n) : BareissState n :=
  match fuel with
  | 0 => state
  | fuel + 1 =>
      if hDone : state.step + 1 < n then
        let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        let pivot := state.matrix[k][k]
        if hp : pivot = 0 then
          { state with singularStep := some state.step }
        else
          let next : BareissState n :=
            { step := state.step + 1
              matrix := stepMatrix state.matrix state.step pivot state.prevPivot
              prevPivot := pivot
              rowSwaps := state.rowSwaps
              singularStep := none }
          noPivotLoop fuel next
      else
        state

/-- With zero fuel, the no-pivot Bareiss loop returns its input state. -/
theorem noPivotLoop_zero_fuel (state : BareissState n) :
    noPivotLoop 0 state = state := by
  rfl

/-- If the current step is already past the last update step, the no-pivot loop
returns its input state. -/
theorem noPivotLoop_done (fuel : Nat) (state : BareissState n)
    (hDone : ¬ state.step + 1 < n) :
    noPivotLoop (fuel + 1) state = state := by
  simp [noPivotLoop, hDone]

/-- If the no-pivot loop sees a zero pivot before completion, it records the
current step as singular. -/
theorem noPivotLoop_singular_branch (fuel : Nat) (state : BareissState n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[state.step][state.step] = 0) :
    noPivotLoop (fuel + 1) state = { state with singularStep := some state.step } := by
  simp [noPivotLoop, hDone, hp]

/-- If the current no-pivot Bareiss pivot is nonzero, one loop iteration applies
`stepMatrix`, advances the step, and recurses on the remaining fuel. -/
theorem noPivotLoop_regular_branch (fuel : Nat) (state : BareissState n)
    (hDone : state.step + 1 < n)
    (hp : state.matrix[state.step][state.step] ≠ 0) :
    noPivotLoop (fuel + 1) state =
      noPivotLoop fuel
        { step := state.step + 1
          matrix := stepMatrix state.matrix state.step state.matrix[state.step][state.step]
            state.prevPivot
          prevPivot := state.matrix[state.step][state.step]
          rowSwaps := state.rowSwaps
          singularStep := none } := by
  simp [noPivotLoop, hDone, hp]

/-- Entries in rows already processed, or in columns strictly before the current
step, are unchanged by subsequent no-pivot loop iterations. -/
theorem noPivotLoop_matrix_entry_of_row_le_or_col_lt (fuel : Nat)
    (state : BareissState n) (i j : Fin n)
    (hfixed : i.val ≤ state.step ∨ j.val < state.step) :
    (noPivotLoop fuel state).matrix[i][j] = state.matrix[i][j] := by
  induction fuel generalizing state with
  | zero =>
      simp [noPivotLoop]
  | succ fuel ih =>
      by_cases hDone : state.step + 1 < n
      · let k : Fin n :=
          ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        by_cases hp : state.matrix[k][k] = 0
        · simp [noPivotLoop_singular_branch fuel state hDone hp]
        · rw [noPivotLoop_regular_branch fuel state hDone]
          · let next : BareissState n :=
              { step := state.step + 1
                matrix := stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot
                prevPivot := state.matrix[state.step][state.step]
                rowSwaps := state.rowSwaps
                singularStep := none }
            change (noPivotLoop fuel next).matrix[i][j] = state.matrix[i][j]
            have hnext : i.val ≤ next.step ∨ j.val < next.step := by
              cases hfixed with
              | inl hi =>
                  exact Or.inl (Nat.le_trans hi (Nat.le_succ state.step))
              | inr hj =>
                  exact Or.inr (Nat.lt_trans hj (Nat.lt_succ_self state.step))
            rw [ih next hnext]
            dsimp [next]
            apply stepMatrix_eq_of_not_update
            · intro htrail
              cases hfixed with
              | inl hi =>
                  exact Nat.not_lt_of_ge hi htrail.1
              | inr hj =>
                  exact Nat.not_lt_of_ge (Nat.le_of_lt hj) htrail.2
            · intro hcol
              cases hfixed with
              | inl hi =>
                  exact Nat.not_lt_of_ge hi hcol.1
              | inr hj =>
                  exact Nat.ne_of_lt hj hcol.2
          · simpa [k] using hp
      · simp [noPivotLoop_done fuel state hDone]

/-- Diagonal entries at or before the current step are unchanged by subsequent
no-pivot loop iterations. -/
theorem noPivotLoop_diag_of_le_step (fuel : Nat) (state : BareissState n)
    (i : Fin n) (hi : i.val ≤ state.step) :
    (noPivotLoop fuel state).matrix[i][i] = state.matrix[i][i] :=
  noPivotLoop_matrix_entry_of_row_le_or_col_lt fuel state i i (Or.inl hi)

/-- The no-pivot loop never changes the row-swap counter. -/
theorem noPivotLoop_rowSwaps (fuel : Nat) (state : BareissState n) :
    (noPivotLoop fuel state).rowSwaps = state.rowSwaps := by
  induction fuel generalizing state with
  | zero =>
      simp [noPivotLoop]
  | succ fuel ih =>
      by_cases hDone : state.step + 1 < n
      · let k : Fin n :=
          ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        by_cases hp : state.matrix[k][k] = 0
        · simp [noPivotLoop_singular_branch fuel state hDone hp]
        · rw [noPivotLoop_regular_branch fuel state hDone]
          · let next : BareissState n :=
              { step := state.step + 1
                matrix := stepMatrix state.matrix state.step
                  state.matrix[state.step][state.step] state.prevPivot
                prevPivot := state.matrix[state.step][state.step]
                rowSwaps := state.rowSwaps
                singularStep := none }
            change (noPivotLoop fuel next).rowSwaps = state.rowSwaps
            rw [ih next]
          · simpa [k] using hp
      · simp [noPivotLoop_done fuel state hDone]

/-- Initial state used by the no-pivot Bareiss recurrence. -/
def noPivotInitialState (M : Matrix Int n n) : BareissState n :=
  { step := 0
    matrix := M
    prevPivot := 1
    rowSwaps := 0
    singularStep := none }

/-- Bareiss elimination with row pivoting. If a column has no nonzero pivot,
the elimination aborts and the determinant is zero. -/
private def pivotLoop (fuel : Nat) (state : BareissState n) : BareissState n :=
  match fuel with
  | 0 => state
  | fuel + 1 =>
      if hDone : state.step + 1 < n then
        let k : Fin n := ⟨state.step, Nat.lt_trans (Nat.lt_succ_self state.step) hDone⟩
        let (M, swaps) :=
          if state.matrix[k][k] = 0 then
            match findPivot? state.matrix k (state.step + 1) with
            | some pivot => (rowSwap state.matrix k pivot, state.rowSwaps + 1)
            | none => (state.matrix, state.rowSwaps)
          else
            (state.matrix, state.rowSwaps)
        let pivot := M[k][k]
        if hp : pivot = 0 then
          { state with matrix := M, rowSwaps := swaps, singularStep := some state.step }
        else
          let next : BareissState n :=
            { step := state.step + 1
              matrix := stepMatrix M state.step pivot state.prevPivot
              prevPivot := pivot
              rowSwaps := swaps
              singularStep := none }
          pivotLoop fuel next
      else
        state

/-- Run the no-pivot Bareiss recurrence and return the final elimination data. -/
def bareissNoPivotData (M : Matrix Int n n) : BareissData n :=
  finish <| noPivotLoop n (noPivotInitialState M)

/-- Determinant computed by the no-pivot Bareiss recurrence. -/
def bareissNoPivot (M : Matrix Int n n) : Int :=
  (bareissNoPivotData M).det

/-- Run the row-pivoted Bareiss elimination and return the final elimination
data together with the swap/sign bookkeeping. -/
def bareissData (M : Matrix Int n n) : BareissData n :=
  let state := bareissArrayState M
  { matrix := rowsToMatrix state.matrix n
    rowSwaps := state.rowSwaps
    singularStep := state.singularStep }

/-- Determinant computed by the row-pivoted Bareiss algorithm. -/
def bareiss (M : Matrix Int n n) : Int :=
  let state := bareissArrayState M
  bareissArrayDet state n

/-- The Bareiss determinant agrees with the generic determinant. -/
theorem bareiss_eq_det (M : Matrix Int n n) :
    bareiss M = det M := by
  sorry

end Matrix
end Hex
