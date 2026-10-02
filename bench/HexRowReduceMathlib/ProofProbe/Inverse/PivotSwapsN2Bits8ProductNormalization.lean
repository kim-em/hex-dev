/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRowReduceMathlib.Tactic
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 0
theorem result : (!![0, 81; 90, 0] : Matrix (Fin 2) (Fin 2) ℚ) * !![0, (1 / 90); (1 / 81), 0] = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

#print axioms result
