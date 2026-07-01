/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGramSchmidt.Int.Invariant
import all HexGramSchmidt.Int.Invariant

public section

/-!
Correspondence between the executable `scaledCoeffRows` pass and the
matrix-level Gram-determinant API for `hex-gram-schmidt`.

This module proves that the array-storage scaled-coefficient loop tracks the
matrix-level no-pivot Bareiss pass entry for entry: the diagonal slots record
the leading Gram determinants (`gramDetVecEntry_eq_gramDet`,
`scaledCoeffRows_diag_toNat_eq_gramDet`) including the zero tail after an early
singular step, and the lower-triangle slots capture the corresponding Bareiss
target-column values. It exposes the determinant base case `gramDet_zero`, the
lower-triangularity of the public matrix (`scaledCoeffs_upper`), and the
lattice-norm helper `vecMul_coeffs_apply_eq_of_zero_above` giving the
top Gram-Schmidt coordinate of a row combination when the later integer
coefficients vanish.
-/
namespace Hex
namespace GramSchmidt.Int
/-- Bareiss-side counterpart of the Schur `j = 0` boundary: at column `0`,
the scaled-coefficient array records the gram entry `gram[i][0]` at every
row `i`. The first `writeScaledColumn` call captures the initial gram column;
subsequent loop iterations advance past column `0` and preserve it. -/
private theorem getArrayEntry_scaledCoeffRows_col_zero
    (b : Matrix Int n m) (i : Nat) :
    getArrayEntry (scaledCoeffRows b) i 0 =
      getArrayEntry (gramRows b) i 0 := by
  by_cases hin : i < n
  · -- In bounds. n ≥ 1 (since `i < n`), so the array loop unfolds at least
    -- one step. The first iteration writes column 0 from `gramRows b`, and
    -- later iterations have `step ≥ 1` so they preserve column 0.
    have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) hin
    obtain ⟨fuel, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h_coeffs_size : (zeroRows (fuel + 1)).size = fuel + 1 := zeroRows_size _
    have h_coeffs_row_size :
        ∀ r, r < fuel + 1 → (zeroRows (fuel + 1))[r]!.size = fuel + 1 :=
      fun r hr => zeroRows_row_size _ r hr
    let initState : ScaledCoeffArrayState :=
      { step := 0, matrix := gramRows b, coeffs := zeroRows (fuel + 1),
        prevPivot := 1 }
    by_cases hi : i = 0
    · -- Diagonal case: (0, 0). Unfold one step and use writeScaledColumn_diag.
      subst hi
      have hrow : (0 : Nat) < (zeroRows (fuel + 1)).size := by
        rw [h_coeffs_size]; exact hn
      have hcol : (0 : Nat) < (zeroRows (fuel + 1))[0]!.size := by
        rw [zeroRows_row_size _ 0 hn]; exact hn
      show getArrayEntry (scaledCoeffArrayLoop (fuel + 1) (fuel + 1) initState).coeffs 0 0
          = getArrayEntry (gramRows b) 0 0
      by_cases hNext : (0 : Nat) + 1 < fuel + 1
      · by_cases hp : getArrayEntry (gramRows b) 0 0 = 0
        · rw [scaledCoeffArrayLoop_singular_branch (n := fuel + 1) fuel initState hn hNext hp]
          exact getArrayEntry_writeScaledColumn_diag _ _ _ _ hrow hcol
        · rw [scaledCoeffArrayLoop_regular_branch (n := fuel + 1) fuel initState hn hNext hp]
          rw [getArrayEntry_scaledCoeffArrayLoop_preserve_col_before_step
                (n := fuel + 1) fuel _ 0 0 (show (0 : Nat) < 0 + 1 by omega)]
          exact getArrayEntry_writeScaledColumn_diag _ _ _ _ hrow hcol
      · rw [scaledCoeffArrayLoop_last_step (n := fuel + 1) fuel initState hn hNext]
        exact getArrayEntry_writeScaledColumn_diag _ _ _ _ hrow hcol
    · -- Strict lower (0 < i < n). Reuse the existing current-col capture lemma.
      have hji : 0 < i := Nat.pos_of_ne_zero hi
      show getArrayEntry (scaledCoeffArrayLoop (fuel + 1) (fuel + 1) initState).coeffs i 0
          = getArrayEntry (gramRows b) i 0
      exact getArrayEntry_scaledCoeffArrayLoop_current_col_written
        (n := fuel + 1) fuel initState i 0 (by rfl) hji hin h_coeffs_size h_coeffs_row_size
  · -- Out of bounds. The array loop never grows `coeffs.size`, so `(i, 0)`
    -- stays at the initial zero (and so does `(gramRows b)[i][0]`).
    have hin' : n ≤ i := Nat.le_of_not_lt hin
    have h_final_size : (scaledCoeffRows b).size = n := by
      unfold scaledCoeffRows
      rw [scaledCoeffArrayLoop_coeffs_size]
      exact zeroRows_size n
    have h_gram_size : (gramRows b).size = n := gramRows_size b
    have h_lhs : getArrayEntry (scaledCoeffRows b) i 0 = 0 := by
      have h_size_le : (scaledCoeffRows b).size ≤ i := h_final_size.symm ▸ hin'
      have h_entry_default : (scaledCoeffRows b)[i]! = (default : Array Int) := by
        rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_none h_size_le, Option.getD_none]
      unfold getArrayEntry
      rw [h_entry_default]
      exact getArrayEntry_default_row 0
    have h_rhs : getArrayEntry (gramRows b) i 0 = 0 := by
      have h_size_le : (gramRows b).size ≤ i := h_gram_size.symm ▸ hin'
      have h_entry_default : (gramRows b)[i]! = (default : Array Int) := by
        rw [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_none h_size_le, Option.getD_none]
      unfold getArrayEntry
      rw [h_entry_default]
      exact getArrayEntry_default_row 0
    rw [h_lhs, h_rhs]

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
        rw [hdist, Matrix.noPivotLoop_zero_fuel,
          getArrayEntry_eq_rowsToMatrix state_array.matrix i j, h_matrix_eq]
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
            rw [rowsToMatrix_stepScaledRows_eq _ _ _ _ h_array_size
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
          rw [h_capture, hdist, Matrix.noPivotLoop_regular_branch _ state_matrix hDone hp]
          rfl

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
  rw [scaledCoeffArrayLoop_singular_branch fuel state_array hArrayStep hArrayNext hp_array,
    getArrayEntry_writeScaledColumn]
  · exact h_coeffs_unwritten i j hsj hji
  · rw [h_step_eq]
    omega

/-- Singular dual of `scaledCoeffArrayLoop_lower_matches_target_column`.
When the matrix-side `noPivotLoop` records a singular step strictly before
reaching column `j`, the array loop halts at the singular column and the
target column is left at its initial (unwritten) zero value. -/
private theorem scaledCoeffArrayLoop_lower_zero
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
            rw [rowsToMatrix_stepScaledRows_eq _ _ _ _ h_array_size
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
            rw [getArrayEntry_writeScaledColumn _ _ _ _ _ _ hc_ne_step]
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
          rw [scaledCoeffArrayLoop_singular_branch fuel' state_array hArrayStep hArrayNext hp_array,
            Matrix.noPivotLoop_singular_branch fuel' state_matrix hDone hp]
          right
          refine ⟨state_matrix.step, rfl, ?_⟩
          by_cases h_ilt : i.val < state_matrix.step
          · right
            refine ⟨h_ilt, ?_⟩
            change getArrayEntry
              (writeScaledColumn state_array.coeffs state_array.matrix n state_array.step) i.val i.val =
              state_matrix.matrix[i][i]
            rw [getArrayEntry_writeScaledColumn _ _ _ _ _ _
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
              rw [getArrayEntry_writeScaledColumn _ _ _ _ _ _
                (show i.val ≠ state_array.step by rw [h_step_eq]; omega)]
              exact h_coeffs_unwritten i.val (Nat.le_of_lt h_igt) i.isLt
        · -- A2: regular branch.
          have hp_array : getArrayEntry state_array.matrix state_array.step state_array.step ≠ 0 := by
            rw [h_pivot_array_eq_matrix]; exact hp
          rw [scaledCoeffArrayLoop_regular_branch fuel' state_array hArrayStep hArrayNext hp_array,
            Matrix.noPivotLoop_regular_branch fuel' state_matrix hDone hp]
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
            rw [rowsToMatrix_stepScaledRows_eq _ _ _ _ h_array_size
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
              rw [getArrayEntry_eq_rowsToMatrix state_array.matrix jFin jFin, h_matrix_eq]
            · have hj_lt : j < state_matrix.step := Nat.lt_of_le_of_ne hj_le hj_eq
              rw [getArrayEntry_writeScaledColumn _ _ _ _ _ _
                (show j ≠ state_array.step by rw [h_step_eq]; omega)]
              exact h_coeffs_processed j hj_lt hjn
          have h_coeffs_unwritten_new :
              ∀ j (_hjs : new_matrix.step ≤ j) (_hjn : j < n),
                getArrayEntry new_array.coeffs j j = 0 := by
            intro j hjs hjn
            show getArrayEntry (writeScaledColumn _ _ _ _) j j = 0
            have hj_gt : state_matrix.step < j := hjs
            rw [getArrayEntry_writeScaledColumn _ _ _ _ _ _
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
            rw [getArrayEntry_writeScaledColumn_diag _ _ _ _ hrow hcol,
              getArrayEntry_eq_rowsToMatrix state_array.matrix i i, h_matrix_eq]
          · by_cases h_ilt : i.val < state_matrix.step
            · change getArrayEntry (writeScaledColumn _ _ _ _) i.val i.val = _
              rw [getArrayEntry_writeScaledColumn _ _ _ _ _ _
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
private theorem gramDetVecEntry_eq_principalSubmatrix_bareiss
    (b : Matrix Int n m) (hquot : StepWitness b) (r : Nat) (hr : r < n) :
    gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
        ⟨r + 1, Nat.succ_lt_succ hr⟩ =
      (Matrix.bareiss
        (Matrix.principalSubmatrix (Matrix.gramMatrix b) (r + 1)
          (Nat.succ_le_of_lt hr))).toNat := by
  let GM := Matrix.gramMatrix b
  let init := Matrix.noPivotInitialState GM
  let data := Matrix.bareissNoPivotData GM
  let i : Fin n := ⟨r, hr⟩
  by_cases h_prefix :
      (Matrix.noPivotLoop r init).singularStep = none
  · have hdiag :=
      bareissNoPivotData_diag_eq_principalSubmatrix_bareiss_of_prefix_nonsingular
        (b := b) r hr (by simpa [GM, init] using h_prefix)
    have h_step_r : (Matrix.noPivotLoop r init).step = r := by
      have h_room : init.step + r + 1 ≤ n := by
        simp [init, Matrix.noPivotInitialState]
        omega
      have h := Matrix.noPivotLoop_step_eq_add_of_singularStep_none
        r init rfl h_room h_prefix
      simpa [init, Matrix.noPivotInitialState] using h
    have h_entry_diag :
        gramDetVecEntry data ⟨r + 1, Nat.succ_lt_succ hr⟩ =
          (data.matrix[i][i]).toNat := by
      have h_split : r + (n - r) = n := by omega
      have h_full :
          Matrix.noPivotLoop n init =
            Matrix.noPivotLoop (n - r) (Matrix.noPivotLoop r init) := by
        simpa [h_split] using Matrix.noPivotLoop_add r (n - r) init
      rcases noPivotLoop_singular_inv (n := n) (n - r)
          (Matrix.noPivotLoop r init) h_prefix with h_none | h_sing
      · have hdata : data.singularStep = none := by
          simpa [data, Matrix.bareissNoPivotData, Matrix.finish, GM, init, h_full] using h_none
        simp [gramDetVecEntry, data, hdata, i]
        rfl
      · rcases h_sing with ⟨k, h_sing_full, h_step_full, h_zero_full, _hk_bound⟩
        have hdata : data.singularStep = some k.val := by
          simpa [data, Matrix.bareissNoPivotData, Matrix.finish, GM, init, h_full] using h_sing_full
        have hmono := noPivotLoop_step_monotone (n - r) (Matrix.noPivotLoop r init)
        have hr_le_k : r ≤ k.val := by
          rw [h_step_r, h_step_full] at hmono
          exact hmono
        by_cases hkr : k.val = r
        · have hlt : k.val < r + 1 := by omega
          have hdata_matrix :
              data.matrix[i][i] =
                (Matrix.noPivotLoop (n - r) (Matrix.noPivotLoop r init)).matrix[i][i] := by
            simp [data, Matrix.bareissNoPivotData, Matrix.finish, GM, init, h_full]
          have hzero_i : data.matrix[i][i] = 0 := by
            have hi_eq : i = k := Fin.ext hkr.symm
            rw [hdata_matrix]
            simpa [hi_eq] using h_zero_full
          simp [gramDetVecEntry, data, hdata, i, hlt]
          simpa [data, i] using (congrArg Int.toNat hzero_i).symm
        · have hlt : ¬ k.val < r + 1 := by omega
          simp [gramDetVecEntry, data, hdata, i, hlt]
          rfl
    calc
      gramDetVecEntry (Matrix.bareissNoPivotData (Matrix.gramMatrix b))
          ⟨r + 1, Nat.succ_lt_succ hr⟩ =
          (data.matrix[i][i]).toNat := by
            simpa [data, GM, i] using h_entry_diag
      _ = (Matrix.bareiss
            (Matrix.principalSubmatrix (Matrix.gramMatrix b) (r + 1)
              (Nat.succ_le_of_lt hr))).toNat := by
            exact congrArg Int.toNat (by simpa [data, GM, i] using hdiag)
  · rcases noPivotLoop_singular_inv (n := n) r init rfl with h_none | h_sing
    · exact False.elim (h_prefix h_none)
    · rcases h_sing with ⟨k, h_sing_r, h_step_r, h_zero_r, h_klt⟩
      have hsr : k.val < r + 1 := by
        have h := noPivotLoop_singularStep_lt (n := n) r init rfl k.val h_sing_r
        simp [init, Matrix.noPivotInitialState] at h
        omega
      have h_full_eq :
          Matrix.noPivotLoop n init = Matrix.noPivotLoop r init := by
        have h_split : n = r + (n - r) := by omega
        have hext :=
          noPivotLoop_extends_singularStep init r (n - r) k
            h_sing_r h_step_r h_zero_r h_klt
        exact (congrArg (fun fuel => Matrix.noPivotLoop fuel init) h_split).trans hext
      have hdata : data.singularStep = some k.val := by
        simpa [data, Matrix.bareissNoPivotData, Matrix.finish, GM, init, h_full_eq] using h_sing_r
      have hleft :
          gramDetVecEntry data ⟨r + 1, Nat.succ_lt_succ hr⟩ = 0 := by
        simp [gramDetVecEntry, data, hdata, hsr]
      have hright :
          (Matrix.bareiss
            (Matrix.principalSubmatrix (Matrix.gramMatrix b) (r + 1)
              (Nat.succ_le_of_lt hr))).toNat = 0 :=
        principalSubmatrix_gram_bareiss_toNat_eq_zero
          (b := b) r hr hquot k.val (by simpa [GM, init] using h_sing_r)
      rw [hright]
      simpa [data, GM] using hleft

/-- The no-pivot Bareiss pass over the full Gram matrix records the same
leading-prefix determinant as the public `gramDet` API at every vector slot. -/
theorem gramDetVecEntry_eq_gramDet
    (b : Matrix Int n m) (hquot : StepWitness b) (k : Nat) (hk : k ≤ n) :
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
              (Matrix.principalSubmatrix (Matrix.gramMatrix b) (r + 1)
                (Nat.succ_le_of_lt hr))).toNat :=
              gramDetVecEntry_eq_principalSubmatrix_bareiss (b := b) hquot r hr
        _ = gramDet b (r + 1) hk := by
              simp [gramDet, GramSchmidt.leadingGramMatrixInt_eq_principalSubmatrix_gram]


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
    (b : Matrix Int n m) (hquot : StepWitness b) (i : Nat) (hi : i < n) :
    (getArrayEntry (scaledCoeffRows b) i i).toNat =
      gramDet b (i + 1) (Nat.succ_le_of_lt hi) := by
  rw [scaledCoeffRows_diag_toNat_eq_gramDetVecEntry (b := b) i hi,
    gramDetVecEntry_eq_gramDet (b := b) hquot (i + 1) (Nat.succ_le_of_lt hi)]

/-- Signed leading-prefix diagonal information from the executable
scaled-coefficient loop: the diagonal slot is either the zero tail after an
early singular no-pivot step, or the Bareiss determinant of the matching
leading Gram prefix. -/
private theorem scaledCoeffRows_diag_eq_zero_or_eq_principalSubmatrix_bareiss
    (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    getArrayEntry (scaledCoeffRows b) i i = 0 ∨
      getArrayEntry (scaledCoeffRows b) i i =
        Matrix.bareiss
          (Matrix.principalSubmatrix (Matrix.gramMatrix b) (i + 1)
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
          (Matrix.principalSubmatrix (Matrix.gramMatrix b) (i + 1)
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
      bareissNoPivotData_diag_eq_principalSubmatrix_bareiss_of_prefix_nonsingular
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
        bareissNoPivotData_diag_eq_principalSubmatrix_bareiss_of_prefix_nonsingular
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

/-- The empty leading Gram determinant is `1`: the determinant of the `0 × 0`
principal Gram minor. This is the base case anchoring the `gramDetVec` diagonal
recurrence (`gramDetVec_eq_gramDet` at `k = 0`). -/
@[simp, grind =] theorem gramDet_zero (b : Matrix Int n m) :
    gramDet b 0 (Nat.zero_le n) = 1 := by
  rfl

/-- Both `scaledCoeffRows` and `scaledCoeffRowsSchur` start from `zeroRows n`
and only write strict-lower / diagonal entries; the upper-triangle slot at
`(i, j)` with `i < j` therefore retains its initial zero value, regardless of
whether `i` and `j` lie inside the array bounds. -/
private theorem getArrayEntry_scaledCoeffRows_above
    (b : Matrix Int n m) (i j : Nat) (hij : i < j) :
    getArrayEntry (scaledCoeffRows b) i j = 0 := by
  unfold scaledCoeffRows
  exact getArrayEntry_scaledCoeffArrayLoop_above n n _
    (fun i' j' hij' => getArrayEntry_zeroRows n i' j') i j hij

/-- The integral scaled Gram-Schmidt coefficient matrix is lower triangular:
every strict-upper-triangle entry (`i < j`) is zero. Callers treating
`scaledCoeffs` as a triangular factor use this to discard above-diagonal terms.
Tagged `@[grind =]` (keyed on the `entry (scaledCoeffs b) i j` term) so the
strict-upper hypothesis `i < j` is discharged by `grind`'s arithmetic when the
vanishing fact is needed. -/
@[grind =] theorem scaledCoeffs_upper (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i < j) :
    GramSchmidt.entry (scaledCoeffs b) ⟨i, hi⟩ ⟨j, hj⟩ = 0 := by
  rw [scaledCoeffs_entry_eq_getArrayEntry]
  exact getArrayEntry_scaledCoeffRowsSchur_upper b i j hij

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
theorem vecMul_coeffs_apply_eq_of_zero_above
    (b : Matrix Int n m) (c : Vector Int n) (k : Fin n)
    (hzero_above : ∀ j : Fin n, k.val < j.val → c[j] = 0) :
    (Matrix.vecMul (Vector.map (fun x : Int => (x : Rat)) c) (coeffs b))[k]
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
      (Matrix.vecMul (Vector.map (fun x : Int => (x : Rat)) c) (coeffs b))[k]
        = (Matrix.vecMul castc (coeffs b))[k] from rfl]
  -- Step 1: rewrite the row-combination entry as a fold over the `k`-th column.
  have hcol :
      (Matrix.vecMul castc (coeffs b))[k]
        = (List.finRange n).foldl
            (fun acc i => acc + (coeffs b)[i][k] * castc[i]) 0 := by
    show ((coeffs b).transpose * castc)[k] = _
    rw [Matrix.getElem_mulVec]
    show (((coeffs b).transpose).row k).dotProduct castc = _
    show (List.finRange n).foldl
        (fun acc i =>
          acc + (((coeffs b).transpose).row k)[i] * castc[i]) 0 = _
    simp only [Matrix.getElem_row, Matrix.getElem_transpose]
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

end GramSchmidt.Int
end Hex
