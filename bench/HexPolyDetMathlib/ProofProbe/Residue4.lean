/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDetMathlib.Tactic
set_option trace.HexMatrix.certificate true

set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000000

theorem result (x y : ZMod 3) :
    Matrix.det !![x, 1, 0, 0; 1, x, 0, 0; 0, 0, y, 1; 0, 0, 1, y] =
      (x ^ 2 - 1) * (y ^ 2 - 1) := by det

#print axioms result
