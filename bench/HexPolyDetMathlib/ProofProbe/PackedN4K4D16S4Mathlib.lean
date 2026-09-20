/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Tactic.NormDet
set_option maxHeartbeats 0
set_option maxRecDepth 100000

set_option profiler true
set_option profiler.threshold 1000000

theorem result (x0 x1 x2 x3 : Int) : Matrix.det (R := Int) (!![(-3) * (1 * (x0 ^ 16) + 2 * (x0) + 3 * (x1) + 1 * (x2)), (-2) * (1 * (x0 ^ 16) + 2 * (x0) + 3 * (x1) + 1 * (x2)), (-3) * (1 * (x0 ^ 16) + 2 * (x0) + 3 * (x1) + 1 * (x2)), (3) * (1 * (x0 ^ 16) + 2 * (x0) + 3 * (x1) + 1 * (x2)); (-1) * (2 * (x1 ^ 16) + 3 * (x1) + 1 * (x2) + 2 * (x3)), (1) * (2 * (x1 ^ 16) + 3 * (x1) + 1 * (x2) + 2 * (x3)), (-3) * (2 * (x1 ^ 16) + 3 * (x1) + 1 * (x2) + 2 * (x3)), (-1) * (2 * (x1 ^ 16) + 3 * (x1) + 1 * (x2) + 2 * (x3)); (3) * (3 * (x2 ^ 16) + 1 * (x2) + 2 * (x3) + 3 * (x0)), (3) * (3 * (x2 ^ 16) + 1 * (x2) + 2 * (x3) + 3 * (x0)), (-2) * (3 * (x2 ^ 16) + 1 * (x2) + 2 * (x3) + 3 * (x0)), (-1) * (3 * (x2 ^ 16) + 1 * (x2) + 2 * (x3) + 3 * (x0)); (3) * (1 * (x3 ^ 16) + 2 * (x3) + 3 * (x0) + 1 * (x1)), (2) * (1 * (x3 ^ 16) + 2 * (x3) + 3 * (x0) + 1 * (x1)), (-1) * (1 * (x3 ^ 16) + 2 * (x3) + 3 * (x0) + 1 * (x1)), (-1) * (1 * (x3 ^ 16) + 2 * (x3) + 3 * (x0) + 1 * (x1))]) = (-26) * (1 * (x0 ^ 16) + 2 * (x0) + 3 * (x1) + 1 * (x2)) * (2 * (x1 ^ 16) + 3 * (x1) + 1 * (x2) + 2 * (x3)) * (3 * (x2 ^ 16) + 1 * (x2) + 2 * (x3) + 3 * (x0)) * (1 * (x3 ^ 16) + 2 * (x3) + 3 * (x0) + 1 * (x1)) := by
  simp only [norm_det] <;> ring

#print axioms result
