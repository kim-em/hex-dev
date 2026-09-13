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

theorem result : Nonempty (HexSmithMathlib.SmithQuotient !![1, 1, -1, 1, -1, 1, -1, 1; 1, 3, -3, 3, 1, 3, -3, 3; 1, -1, 9, 7, -11, -9, 9, -9; 1, -1, -7, 23, 37, 39, -39, 39; -1, -3, -5, -43, -25, -27, 27, -27; -1, 1, -9, 25, 43, 41, -41, 41; -1, -3, -5, 21, 39, 37, -37, 37; 1, -1, 9, 39, 21, 23, -23, 23] 4 ![1, 2, 8, 32]) := by smith

#print axioms result
