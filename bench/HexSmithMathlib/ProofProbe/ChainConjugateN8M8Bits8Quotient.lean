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

theorem result : Nonempty (HexSmithMathlib.SmithQuotient !![1, -1, -1, 1, 1, -1, 1, 1; -1, 2, 2, -2, 0, 2, 0, -2; 1, 0, 2, -2, 0, -2, 0, 2; 1, 0, -2, 4, 6, 4, 6, -4; -1, 2, 0, 2, 8, 2, 8, -2; 1, -2, -4, 6, 8, 2, 12, -2; -1, 0, -2, 0, -6, 8, 6, 0; -1, 0, 2, -4, -2, -4, 10, 28] 8 ![1, 1, 2, 2, 4, 4, 8, 16]) := by smith

#print axioms result
