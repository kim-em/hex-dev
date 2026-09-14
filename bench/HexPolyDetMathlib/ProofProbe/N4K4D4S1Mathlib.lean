/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Tactic.NormDet

set_option maxHeartbeats 0
set_option maxRecDepth 100000

-- Computational performance owner: HexPolyDet.
theorem result (x0 x1 x2 x3 : Int) : Matrix.det (R := Int) (!![(-3) * (1 * (x0 ^ 4)), (-2) * (1 * (x0 ^ 4)), (-3) * (1 * (x0 ^ 4)), (3) * (1 * (x0 ^ 4)); (-1) * (2 * (x1 ^ 4)), (1) * (2 * (x1 ^ 4)), (-3) * (2 * (x1 ^ 4)), (-1) * (2 * (x1 ^ 4)); (3) * (3 * (x2 ^ 4)), (3) * (3 * (x2 ^ 4)), (-2) * (3 * (x2 ^ 4)), (-1) * (3 * (x2 ^ 4)); (3) * (1 * (x3 ^ 4)), (2) * (1 * (x3 ^ 4)), (-1) * (1 * (x3 ^ 4)), (-1) * (1 * (x3 ^ 4))]) = (-26) * (1 * (x0 ^ 4)) * (2 * (x1 ^ 4)) * (3 * (x2 ^ 4)) * (1 * (x3 ^ 4)) := by
  simp only [norm_det] <;> ring

#print axioms result
