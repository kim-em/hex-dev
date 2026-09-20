/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Tactic.NormDet

set_option maxHeartbeats 0
set_option maxRecDepth 100000

-- Computational performance owner: HexPolyDet.
set_option profiler true
set_option profiler.threshold 1000000

theorem result (x0 x1 : Int) : Matrix.det (R := Int) (!![(-3) * (1 * (x0 ^ 4) + 2 * (x0) + 3 * (x1) + 1 * (x0 ^ 2 * x1 ^ 2)), (-2) * (1 * (x0 ^ 4) + 2 * (x0) + 3 * (x1) + 1 * (x0 ^ 2 * x1 ^ 2)), (-3) * (1 * (x0 ^ 4) + 2 * (x0) + 3 * (x1) + 1 * (x0 ^ 2 * x1 ^ 2)), (3) * (1 * (x0 ^ 4) + 2 * (x0) + 3 * (x1) + 1 * (x0 ^ 2 * x1 ^ 2)); (-1) * (2 * (x1 ^ 4) + 3 * (x1) + 1 * (x0) + 2 * (x0 ^ 2)), (1) * (2 * (x1 ^ 4) + 3 * (x1) + 1 * (x0) + 2 * (x0 ^ 2)), (-3) * (2 * (x1 ^ 4) + 3 * (x1) + 1 * (x0) + 2 * (x0 ^ 2)), (-1) * (2 * (x1 ^ 4) + 3 * (x1) + 1 * (x0) + 2 * (x0 ^ 2)); (3) * (3 * (x0 ^ 4) + 1 * (x0) + 2 * (x1) + 3 * (x0 ^ 2 * x1)), (3) * (3 * (x0 ^ 4) + 1 * (x0) + 2 * (x1) + 3 * (x0 ^ 2 * x1)), (-2) * (3 * (x0 ^ 4) + 1 * (x0) + 2 * (x1) + 3 * (x0 ^ 2 * x1)), (-1) * (3 * (x0 ^ 4) + 1 * (x0) + 2 * (x1) + 3 * (x0 ^ 2 * x1)); (3) * (1 * (x1 ^ 4) + 2 * (x1) + 3 * (x0) + 1 * (x0 ^ 4)), (2) * (1 * (x1 ^ 4) + 2 * (x1) + 3 * (x0) + 1 * (x0 ^ 4)), (-1) * (1 * (x1 ^ 4) + 2 * (x1) + 3 * (x0) + 1 * (x0 ^ 4)), (-1) * (1 * (x1 ^ 4) + 2 * (x1) + 3 * (x0) + 1 * (x0 ^ 4))]) = (-26) * (1 * (x0 ^ 4) + 2 * (x0) + 3 * (x1) + 1 * (x0 ^ 2 * x1 ^ 2)) * (2 * (x1 ^ 4) + 3 * (x1) + 1 * (x0) + 2 * (x0 ^ 2)) * (3 * (x0 ^ 4) + 1 * (x0) + 2 * (x1) + 3 * (x0 ^ 2 * x1)) * (1 * (x1 ^ 4) + 2 * (x1) + 3 * (x0) + 1 * (x0 ^ 4)) := by
  simp only [norm_det] <;> ring

#print axioms result
