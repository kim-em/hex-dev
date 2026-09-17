/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRowReduceMathlib.Tactic
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 0
theorem result : (!![(6 / 11), (-6 / 11); (-6 / 11), (49 / 33)] : Matrix (Fin 2) (Fin 2) ℚ) * !![(539 / 186), (33 / 31); (33 / 31), (33 / 31)] = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

#print axioms result
