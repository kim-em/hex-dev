/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRowReduceMathlib.Tactic
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 0
theorem result : (!![(12 / 17), (12 / 17), (12 / 17), (-12 / 17), (12 / 17), (-12 / 17), (12 / 17), (12 / 17); (-12 / 17), (-1 / 17), (-23 / 17), (1 / 17), (-1 / 17), (23 / 17), (-23 / 17), (-1 / 17); (12 / 17), (1 / 17), (31 / 17), (7 / 17), (-7 / 17), (-31 / 17), (31 / 17), (-7 / 17); (-12 / 17), (-1 / 17), (-31 / 17), (6 / 17), (-6 / 17), (44 / 17), (-18 / 17), (-6 / 17)] : Matrix (Fin 4) (Fin 8) ℚ).mulVec ![(1 / 3), (-1 / 3), (-1 / 3), (2 / 3), (-1 / 3), (-1 / 3), (1 / 3), (-1 / 3)] = ![(-12 / 17), (-10 / 17), (70 / 51), (-6 / 17)] := by
  ext i; fin_cases i <;> norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]

#print axioms result
