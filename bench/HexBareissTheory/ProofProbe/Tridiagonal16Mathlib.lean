/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Tactic.NormDet

/-! `Tridiagonal16Mathlib`: the `tridiagonal-16` family, a `16 × 16` literal over `ℤ`, proved by `eval_det`. -/

set_option maxHeartbeats 0

theorem result : Matrix.det (R := ℤ) !![8, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 3, 5, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, -7, 9, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 1, 5, -9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 7, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 9, 7, -7, 0, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 4, 3, -9, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 3, 3, 0, 0, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 8, 8, 8, 0, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 6, 5, -2, 0, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4, 2, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 9, 5, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -6, 8, -9, 0, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 3, 1, 0; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 7, 9; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 2] = -9841364648448 := by eval_det

#print axioms result
