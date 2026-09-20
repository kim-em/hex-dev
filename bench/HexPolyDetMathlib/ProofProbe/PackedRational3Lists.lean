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
set_option hex.det.checker 1
set_option profiler true
set_option profiler.threshold 1000000

theorem result (x0 x1 : Rat) : Matrix.det (R := Rat) (!![((-2) * (1 * (x0 ^ 2) + 2 * (x0) + 3 * (x1) + 1 * (1))) / 2, ((3) * (1 * (x0 ^ 2) + 2 * (x0) + 3 * (x1) + 1 * (1))) / 2, ((-2) * (1 * (x0 ^ 2) + 2 * (x0) + 3 * (x1) + 1 * (1))) / 2; ((-3) * (2 * (x1 ^ 2) + 3 * (x1) + 1 * (x0) + 2 * (1))) / 3, ((1) * (2 * (x1 ^ 2) + 3 * (x1) + 1 * (x0) + 2 * (1))) / 3, ((3) * (2 * (x1 ^ 2) + 3 * (x1) + 1 * (x0) + 2 * (1))) / 3; ((-1) * (3 * (x0 ^ 2) + 1 * (x0) + 2 * (x1) + 3 * (x1 ^ 2))) / 4, ((-3) * (3 * (x0 ^ 2) + 1 * (x0) + 2 * (x1) + 3 * (x1 ^ 2))) / 4, ((1) * (3 * (x0 ^ 2) + 1 * (x0) + 2 * (x1) + 3 * (x1 ^ 2))) / 4]) = ((-40) * (1 * (x0 ^ 2) + 2 * (x0) + 3 * (x1) + 1 * (1)) * (2 * (x1 ^ 2) + 3 * (x1) + 1 * (x0) + 2 * (1)) * (3 * (x0 ^ 2) + 1 * (x0) + 2 * (x1) + 3 * (x1 ^ 2))) / 24 := by
  det

#print axioms result
