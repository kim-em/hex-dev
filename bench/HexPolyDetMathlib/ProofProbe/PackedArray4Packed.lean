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

theorem result (x0 : Int) : Matrix.det (R := Int) (Matrix.ofArray (m := 4) (n := 4) #[x0, 1, 0, 0, 1, x0, 1, 0, 0, 1, x0, 1, 0, 0, 1, x0] rfl) = x0 ^ 4 - 3 * x0 ^ 2 + 1 := by
  det

#print axioms result
