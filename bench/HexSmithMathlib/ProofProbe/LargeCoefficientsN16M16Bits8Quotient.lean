/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexSmithMathlib.Tactic

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 1000000
set_option trace.HexMatrix.certificate true

theorem result : Nonempty (HexSmithMathlib.SmithQuotient !![1, -1, 1, -1, 1, -1, 1, -1, -1, 1, 1, -1, 1, -1, 1, 1; 1, 0, 2, 0, 0, 0, 0, -2, -2, 0, 0, -2, 2, -2, 0, 0; 1, 0, 3, -1, 1, 1, 1, -1, -1, 1, 1, -1, 3, -1, -1, 1; -1, 0, -3, 2, 0, 0, 0, 2, 0, 0, -2, 2, -2, 2, 0, 0; -1, 0, -1, 0, 3, 3, 3, 3, 3, 1, -1, 5, -1, 5, -1, 3; -1, 0, -1, 0, 1, 3, 3, 3, 3, 5, -1, 5, 3, 5, -1, -1; 1, 0, 1, 0, -1, -3, -1, -1, -5, -7, -1, -3, -1, -7, 3, -1; 1, 0, 1, 0, -1, -3, -5, -3, -3, -5, 5, -5, -3, -5, -3, 1; 1, -2, -1, -2, 1, -5, 1, 3, -3, -9, 1, -1, 1, -5, 5, 1; -1, 0, -1, -2, -1, 1, -1, -3, 7, 11, 1, 3, -3, 3, 1, -3; 1, 0, 1, 0, -3, -5, -3, 3, -11, -7, 11, -7, -5, -15, -9, -1; -1, 2, 1, 0, -1, 1, -1, 5, -5, -9, 9, 3, -3, -13, -7, -3; -1, 2, 1, 0, -3, 3, 1, 3, -3, -3, 7, -3, -1, 1, -17, 3; 1, -2, 1, -2, 3, 1, 3, -3, 7, 11, 1, -9, -7, 7, -3, 5; -1, 0, -3, 0, -1, -3, -5, 1, 3, -5, -3, -1, 1, 7, 5, 13; 1, -2, 1, -4, 3, 1, 3, -3, 7, 3, 5, 3, 1, -13, 17, 13] 16 ![1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 8]) := by smith

#print axioms result
