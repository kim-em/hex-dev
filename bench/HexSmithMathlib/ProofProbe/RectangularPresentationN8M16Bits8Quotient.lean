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

theorem result : Nonempty (HexSmithMathlib.SmithQuotient !![1, 1, 1, 1, 1, 1, -1, -1, 1, -1, 1, 1, -1, -1, -1, -1; -1, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, -2, 0, 2, 2, 0; -1, 0, 2, -2, 2, 0, 2, -2, -2, 2, -2, -4, 2, 0, 0, 2; -1, -2, -4, 2, -2, -4, -2, 2, -2, 2, -2, 0, -2, 4, 0, 2; 1, 0, -2, 4, 4, -6, -8, 4, -4, 4, 4, 6, -8, 6, 2, 4; 1, 2, 0, 2, -6, 8, -2, -6, 14, -14, -2, -4, -2, 0, -4, -14; -1, -2, 0, -6, -6, 12, 14, 2, 14, -14, -2, 0, 14, 4, 0, 2; -1, -2, -4, 2, 2, -12, 6, 34, 14, -14, 30, 0, -10, -4, 0, 2] 8 ![1, 1, 2, 2, 4, 4, 8, 16]) := by smith

#print axioms result
