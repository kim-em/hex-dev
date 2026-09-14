/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDetMathlib.Tactic

set_option maxHeartbeats 0
set_option maxRecDepth 100000

-- Computational performance owner: HexPolyDet.
theorem result (x0 x1 : Int) : Matrix.det (R := Int) !![(-2) * (1 * (x0)), (3) * (1 * (x0)), (-2) * (1 * (x0)); (-3) * (2 * (x1)), (1) * (2 * (x1)), (3) * (2 * (x1)); (-2) * (1 * (x0)), (3) * (1 * (x0)), (-2) * (1 * (x0))] = 0 := by
  det

#print axioms result
