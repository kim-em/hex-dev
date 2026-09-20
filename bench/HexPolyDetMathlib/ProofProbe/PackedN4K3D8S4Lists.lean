/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDetMathlib.Tactic
set_option maxHeartbeats 0
set_option maxRecDepth 100000

set_option trace.HexMatrix.certificate true
set_option hex.det.checker 1
set_option profiler true
set_option profiler.threshold 1000000

theorem result (x0 x1 x2 : Int) : Matrix.det (R := Int) (!![(-3) * (1 * (x0 ^ 8) + 2 * (x0) + 3 * (x1) + 1 * (x2)), (-2) * (1 * (x0 ^ 8) + 2 * (x0) + 3 * (x1) + 1 * (x2)), (-3) * (1 * (x0 ^ 8) + 2 * (x0) + 3 * (x1) + 1 * (x2)), (3) * (1 * (x0 ^ 8) + 2 * (x0) + 3 * (x1) + 1 * (x2)); (-1) * (2 * (x1 ^ 8) + 3 * (x1) + 1 * (x2) + 2 * (x0)), (1) * (2 * (x1 ^ 8) + 3 * (x1) + 1 * (x2) + 2 * (x0)), (-3) * (2 * (x1 ^ 8) + 3 * (x1) + 1 * (x2) + 2 * (x0)), (-1) * (2 * (x1 ^ 8) + 3 * (x1) + 1 * (x2) + 2 * (x0)); (3) * (3 * (x2 ^ 8) + 1 * (x2) + 2 * (x0) + 3 * (x1)), (3) * (3 * (x2 ^ 8) + 1 * (x2) + 2 * (x0) + 3 * (x1)), (-2) * (3 * (x2 ^ 8) + 1 * (x2) + 2 * (x0) + 3 * (x1)), (-1) * (3 * (x2 ^ 8) + 1 * (x2) + 2 * (x0) + 3 * (x1)); (3) * (1 * (x0 ^ 8) + 2 * (x0) + 3 * (x1) + 1 * (x2)), (2) * (1 * (x0 ^ 8) + 2 * (x0) + 3 * (x1) + 1 * (x2)), (-1) * (1 * (x0 ^ 8) + 2 * (x0) + 3 * (x1) + 1 * (x2)), (-1) * (1 * (x0 ^ 8) + 2 * (x0) + 3 * (x1) + 1 * (x2))]) = (-26) * (1 * (x0 ^ 8) + 2 * (x0) + 3 * (x1) + 1 * (x2)) * (2 * (x1 ^ 8) + 3 * (x1) + 1 * (x2) + 2 * (x0)) * (3 * (x2 ^ 8) + 1 * (x2) + 2 * (x0) + 3 * (x1)) * (1 * (x0 ^ 8) + 2 * (x0) + 3 * (x1) + 1 * (x2)) := by
  det

#print axioms result
