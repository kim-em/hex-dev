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

theorem result : Nonempty (HexSmithMathlib.SmithQuotient !![1, -1, -1, 1, -1, -1, -1, -1; -1, 3, 3, 1, 3, 3, -1, -1; 1, -3, 5, -9, 5, -11, -7, 9; -1, 3, 11, 25, 43, 27, -41, -25] 4 ![1, 2, 8, 32]) := by smith

#print axioms result
