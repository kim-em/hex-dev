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

theorem result : Nonempty (HexSmithMathlib.SmithQuotient !![1, -1, 1, 1, 1, -1, -1, -1; -1, 2, 0, 0, 0, 2, 2, 2; 1, 0, 4, 4, 4, -2, 2, 2; 1, -2, 2, 4, 0, -2, -2, 2; 1, 0, 0, 2, 2, 8, 0, 4; 1, 0, 4, 2, 10, 4, 12, 8; -1, 0, -4, -2, -2, 12, 12, 16; 1, 0, 0, -2, -2, 0, -8, 4; -1, 0, 0, -2, -2, -4, -4, -24; 1, -2, 2, 4, 4, 6, -2, 18; -1, 2, -2, -4, -4, 2, -6, 6; 1, 0, 4, 6, 6, 0, -8, -20; 1, -2, -2, 0, 0, 10, -6, -18; 1, 0, 0, 2, 2, 12, -4, -16; 1, -2, 2, 0, 0, -14, -14, -2; -1, 2, -2, 0, -8, 6, -10, -22] 8 ![1, 1, 2, 2, 4, 4, 8, 16]) := by smith

#print axioms result
