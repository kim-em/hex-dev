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

theorem result : Nonempty (HexSmithMathlib.SmithQuotient !![1, -1, -1, 1, 1, 1, -1, -1, 1, -1, -1, 1, 1, 1, -1, -1; 1, 0, 0, 2, 2, 0, -2, 0, 2, 0, -2, 2, 2, 2, 0, 0; 1, 0, 1, 3, 3, 1, -3, -1, 1, -1, -3, 3, 3, 1, -1, -1; 1, 0, -1, 2, 2, -2, 0, 2, 4, 2, -2, 2, 0, 2, 0, 0; 1, 0, 1, 4, 5, -1, -1, -1, 1, -1, -5, 3, 3, 1, -3, -3; 1, 0, -1, 2, 3, -1, 3, -1, 5, -1, -1, -1, -1, 1, -3, 1; -1, 2, 3, 0, 1, -3, -1, -1, -3, 3, -5, 3, 7, 5, 5, 1; 1, 0, -1, 2, 1, 1, -1, 5, 3, -3, 1, -3, -7, -5, -1, 3; -1, 0, 1, 0, -1, 3, 5, -1, 3, 1, 1, 1, -3, -5, 3, 3; -1, 0, 1, -2, -3, 1, -1, 1, -3, 5, 1, 5, 1, 3, 7, 3; -1, 2, 1, -2, -1, -5, -3, 3, -5, -1, 3, -1, -1, 5, -3, -7; -1, 0, -1, -2, -3, -3, -1, 9, -7, 1, 5, 5, -19, 3, -1, 3; -1, 0, -1, -4, -3, -3, -1, 5, -7, -3, 5, -7, 5, 3, 3, -17; 1, 0, 1, 2, 1, 1, -5, -3, 1, 1, -11, 5, 5, 3, 11, 15; 1, -2, -3, -2, -1, -1, 1, -5, 3, 7, 7, 15, 3, 21, 5, -15; 1, -2, -3, -2, -3, 1, -5, 1, -3, -3, -3, -3, -3, -1, 3, 23] 16 ![1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 4, 4, 4, 4, 8]) := by smith

#print axioms result
