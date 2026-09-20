/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDetMathlib.Tactic

set_option trace.HexMatrix.certificate true
set_option hex.det.checker 2
set_option profiler true
set_option profiler.threshold 1000000

theorem result (x : Int) (hx : x = 1) : Matrix.det !![x, 1; 1, x] = 0 := by
  have h : Matrix.det !![x, 1; 1, x] = x ^ 2 - 1 := by
    det
  rw [h, hx]
  rfl
#print axioms result
