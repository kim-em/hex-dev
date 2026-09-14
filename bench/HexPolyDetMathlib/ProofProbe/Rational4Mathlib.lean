/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Tactic.NormDet

set_option maxHeartbeats 0
set_option maxRecDepth 100000

-- Computational performance owner: HexPolyDet.
theorem result (x0 x1 : Rat) : Matrix.det (R := Rat) (!![((-3) * (1 * (x0 ^ 2) + 2 * (x0) + 3 * (x1) + 1 * (1))) / 2, ((-2) * (1 * (x0 ^ 2) + 2 * (x0) + 3 * (x1) + 1 * (1))) / 2, ((-3) * (1 * (x0 ^ 2) + 2 * (x0) + 3 * (x1) + 1 * (1))) / 2, ((3) * (1 * (x0 ^ 2) + 2 * (x0) + 3 * (x1) + 1 * (1))) / 2; ((-1) * (2 * (x1 ^ 2) + 3 * (x1) + 1 * (x0) + 2 * (1))) / 3, ((1) * (2 * (x1 ^ 2) + 3 * (x1) + 1 * (x0) + 2 * (1))) / 3, ((-3) * (2 * (x1 ^ 2) + 3 * (x1) + 1 * (x0) + 2 * (1))) / 3, ((-1) * (2 * (x1 ^ 2) + 3 * (x1) + 1 * (x0) + 2 * (1))) / 3; ((3) * (3 * (x0 ^ 2) + 1 * (x0) + 2 * (x1) + 3 * (x1 ^ 2))) / 4, ((3) * (3 * (x0 ^ 2) + 1 * (x0) + 2 * (x1) + 3 * (x1 ^ 2))) / 4, ((-2) * (3 * (x0 ^ 2) + 1 * (x0) + 2 * (x1) + 3 * (x1 ^ 2))) / 4, ((-1) * (3 * (x0 ^ 2) + 1 * (x0) + 2 * (x1) + 3 * (x1 ^ 2))) / 4; ((3) * (1 * (x1 ^ 2) + 2 * (x1) + 3 * (x0) + 1 * (x0 ^ 2))) / 5, ((2) * (1 * (x1 ^ 2) + 2 * (x1) + 3 * (x0) + 1 * (x0 ^ 2))) / 5, ((-1) * (1 * (x1 ^ 2) + 2 * (x1) + 3 * (x0) + 1 * (x0 ^ 2))) / 5, ((-1) * (1 * (x1 ^ 2) + 2 * (x1) + 3 * (x0) + 1 * (x0 ^ 2))) / 5]) = ((-26) * (1 * (x0 ^ 2) + 2 * (x0) + 3 * (x1) + 1 * (1)) * (2 * (x1 ^ 2) + 3 * (x1) + 1 * (x0) + 2 * (1)) * (3 * (x0 ^ 2) + 1 * (x0) + 2 * (x1) + 3 * (x1 ^ 2)) * (1 * (x1 ^ 2) + 2 * (x1) + 3 * (x0) + 1 * (x0 ^ 2))) / 120 := by
  simp only [norm_det] <;> ring

#print axioms result
