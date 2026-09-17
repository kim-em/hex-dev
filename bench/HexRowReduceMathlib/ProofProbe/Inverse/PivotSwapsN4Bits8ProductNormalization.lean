/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRowReduceMathlib.Tactic
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 0
theorem result : (!![0, 0, 0, 8; 0, 0, 31, 0; 0, 4, 0, 0; 31, 0, 0, 0] : Matrix (Fin 4) (Fin 4) ℚ) * !![0, 0, 0, (1 / 31); 0, 0, (1 / 4), 0; 0, (1 / 31), 0, 0; (1 / 8), 0, 0, 0] = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

#print axioms result
