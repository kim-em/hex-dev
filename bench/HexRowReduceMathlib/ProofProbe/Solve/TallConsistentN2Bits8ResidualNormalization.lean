/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRowReduceMathlib.Tactic
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 0
theorem result : (!![(20 / 33), (-20 / 33); (-20 / 33), (49 / 33); (20 / 33), (-49 / 33); (-20 / 33), (-3 / 11)] : Matrix (Fin 4) (Fin 2) ℚ).mulVec ![(-2 / 3), (-2 / 3)] = ![0, (-58 / 99), (58 / 99), (58 / 99)] := by
  ext i; fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

#print axioms result
