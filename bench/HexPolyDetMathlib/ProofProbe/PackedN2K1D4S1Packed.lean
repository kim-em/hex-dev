/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDetMathlib.Tactic

set_option maxHeartbeats 0
set_option maxRecDepth 100000

-- Computational performance owner: HexPolyDet.
set_option trace.HexMatrix.certificate true
set_option hex.det.checker 2
set_option profiler true
set_option profiler.threshold 1000000

theorem result (x0 : Int) : Matrix.det (R := Int) (!![(2) * (1 * (x0 ^ 4)), (-3) * (1 * (x0 ^ 4)); (-1) * (2 * (x0 ^ 4)), (-2) * (2 * (x0 ^ 4))]) = (-7) * (1 * (x0 ^ 4)) * (2 * (x0 ^ 4)) := by
  det

#print axioms result
