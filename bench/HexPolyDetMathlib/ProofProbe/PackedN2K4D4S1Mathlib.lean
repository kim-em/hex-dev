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

theorem result (x0 x1 x2 x3 : Int) : Matrix.det (R := Int) (!![(2) * (x0 * x1 ^ 3), (-3) * (x0 * x1 ^ 3); (-1) * (x2 * x3 ^ 3), (-2) * (x2 * x3 ^ 3)]) = (-7) * (x0 * x1 ^ 3) * (x2 * x3 ^ 3) := by
  simp only [norm_det] <;> ring

#print axioms result
