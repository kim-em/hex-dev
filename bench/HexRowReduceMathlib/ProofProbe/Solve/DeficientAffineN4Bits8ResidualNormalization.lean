/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRowReduceMathlib.Tactic
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 0
theorem result : (!![(6 / 11), (6 / 11), (-6 / 11), (-6 / 11); (-6 / 11), (10 / 33), (-10 / 33), (46 / 33); (-6 / 11), (-46 / 33), (46 / 33), (-10 / 33); (-6 / 11), (-46 / 33), (46 / 33), (-10 / 33)] : Matrix (Fin 4) (Fin 4) ℚ).mulVec ![(-1 / 3), (-1 / 3), (-1 / 3), (2 / 3)] = ![(-6 / 11), (10 / 9), (-2 / 99), (-2 / 99)] := by
  ext i; fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

#print axioms result
