/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Tactic.NormDet

/-! `Rational8Mathlib`: the `rational-8` family, a `8 × 8` literal over `ℚ`, proved by `eval_det`. -/

set_option maxHeartbeats 0

theorem result : Matrix.det (R := ℚ) !![16 / 3, 19 / 3, 13 / 6, -19 / 2, -7 / 6, 8, -3 / 4, 10; -11 / 2, -2, 15, -19 / 2, 2, 14, 5, -14; -19, 8 / 3, 11, 1, -4 / 3, -9, 4, 0; -3, 1, 19 / 4, -13, -5 / 4, 0, -1 / 4, 4; 1 / 3, -1 / 2, -8 / 3, -9, 1, 18, 13 / 4, -18; 10, -9 / 4, 15 / 4, -5 / 4, 19 / 2, -5 / 2, -13 / 2, 7 / 4; 8 / 3, 3, -5, -15, 2, -4, -9, -15 / 4; -17 / 6, 1 / 6, 1 / 4, 5 / 4, 9, 5, 5 / 2, -3 / 2] = 1767927578471 / 36864 := by eval_det

#print axioms result
