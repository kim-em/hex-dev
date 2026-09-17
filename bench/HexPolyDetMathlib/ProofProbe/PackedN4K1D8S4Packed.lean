/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDetMathlib.Tactic
set_option maxHeartbeats 0
set_option maxRecDepth 100000

set_option trace.HexMatrix.certificate true
set_option hex.det.checker 2
set_option profiler true
set_option profiler.threshold 1000000

theorem result (x0 : Int) : Matrix.det (R := Int) (!![(-3) * (1 * (x0 ^ 8) + 2 * (x0) + 3 * (x0 ^ 3) + 1 * (x0 ^ 2)), (-2) * (1 * (x0 ^ 8) + 2 * (x0) + 3 * (x0 ^ 3) + 1 * (x0 ^ 2)), (-3) * (1 * (x0 ^ 8) + 2 * (x0) + 3 * (x0 ^ 3) + 1 * (x0 ^ 2)), (3) * (1 * (x0 ^ 8) + 2 * (x0) + 3 * (x0 ^ 3) + 1 * (x0 ^ 2)); (-1) * (2 * (x0 ^ 8) + 3 * (x0) + 1 * (x0 ^ 2) + 2 * (x0 ^ 6)), (1) * (2 * (x0 ^ 8) + 3 * (x0) + 1 * (x0 ^ 2) + 2 * (x0 ^ 6)), (-3) * (2 * (x0 ^ 8) + 3 * (x0) + 1 * (x0 ^ 2) + 2 * (x0 ^ 6)), (-1) * (2 * (x0 ^ 8) + 3 * (x0) + 1 * (x0 ^ 2) + 2 * (x0 ^ 6)); (3) * (3 * (x0 ^ 8) + 1 * (x0) + 2 * (1) + 3 * (x0 ^ 4)), (3) * (3 * (x0 ^ 8) + 1 * (x0) + 2 * (1) + 3 * (x0 ^ 4)), (-2) * (3 * (x0 ^ 8) + 1 * (x0) + 2 * (1) + 3 * (x0 ^ 4)), (-1) * (3 * (x0 ^ 8) + 1 * (x0) + 2 * (1) + 3 * (x0 ^ 4)); (3) * (1 * (x0 ^ 8) + 2 * (x0) + 3 * (x0 ^ 5) + 1 * (1)), (2) * (1 * (x0 ^ 8) + 2 * (x0) + 3 * (x0 ^ 5) + 1 * (1)), (-1) * (1 * (x0 ^ 8) + 2 * (x0) + 3 * (x0 ^ 5) + 1 * (1)), (-1) * (1 * (x0 ^ 8) + 2 * (x0) + 3 * (x0 ^ 5) + 1 * (1))]) = (-26) * (1 * (x0 ^ 8) + 2 * (x0) + 3 * (x0 ^ 3) + 1 * (x0 ^ 2)) * (2 * (x0 ^ 8) + 3 * (x0) + 1 * (x0 ^ 2) + 2 * (x0 ^ 6)) * (3 * (x0 ^ 8) + 1 * (x0) + 2 * (1) + 3 * (x0 ^ 4)) * (1 * (x0 ^ 8) + 2 * (x0) + 3 * (x0 ^ 5) + 1 * (1)) := by
  det

#print axioms result
