/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Tactic.NormDet

set_option maxHeartbeats 0
set_option maxRecDepth 100000

-- Computational performance owner: HexPolyDet.
theorem result (x0 : Int) : Matrix.det (R := Int) (!![(2) * (1 * (x0 ^ 4) + 2 * (x0) + 3 * (x0 ^ 2) + 1 * (x0 ^ 3)), (-3) * (1 * (x0 ^ 4) + 2 * (x0) + 3 * (x0 ^ 2) + 1 * (x0 ^ 3)); (-1) * (2 * (x0 ^ 4) + 3 * (x0) + 1 * (x0 ^ 2) + 2 * (1)), (-2) * (2 * (x0 ^ 4) + 3 * (x0) + 1 * (x0 ^ 2) + 2 * (1))]) = (-7) * (1 * (x0 ^ 4) + 2 * (x0) + 3 * (x0 ^ 2) + 1 * (x0 ^ 3)) * (2 * (x0 ^ 4) + 3 * (x0) + 1 * (x0 ^ 2) + 2 * (1)) := by
  simp only [norm_det] <;> ring

#print axioms result
