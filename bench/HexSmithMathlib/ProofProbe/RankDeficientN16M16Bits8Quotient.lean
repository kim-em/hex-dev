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

theorem result : Nonempty (HexSmithMathlib.SmithQuotient !![1, 1, 1, 1, 1, 1, 1, 1, 1, -1, -1, -1, -1, -1, 1, -1; 1, 2, 2, 0, 2, 2, 0, 0, 2, 0, -2, -2, -2, -2, 0, 0; 1, 0, 2, 4, -2, 2, 0, 4, 2, -4, -2, -2, 2, -2, 4, -4; -1, 0, -2, -2, 0, -4, 2, -2, -4, 6, 0, 4, 0, 4, -2, 6; 1, 0, 2, 2, 4, 0, -6, 6, 0, -2, -4, 0, -4, 0, 6, -2; 1, 0, 2, 2, -4, 12, -2, 2, 4, -14, 8, -4, 8, -12, 2, -14; 1, 0, -2, -2, 8, 0, 2, 14, -16, 6, 12, 0, 4, -8, 14, 6; -1, 0, 2, 2, -8, 0, -2, 2, 0, 10, 4, -16, 12, 24, -30, 10; 1, 2, 4, 4, 2, -6, 8, 28, -22, 32, 10, -26, 18, 14, -4, 32; 1, 2, 0, 0, 6, -2, 4, 32, -34, 28, 22, -14, 22, 10, 0, 28; 1, 2, 4, 0, -2, 6, -4, 0, 6, 4, 6, -22, 6, 18, -32, 4; 1, 0, -2, 2, -4, 4, -2, -22, 20, -30, -16, 28, -16, -12, 10, -30; 1, 2, 0, -4, 10, -6, -8, 4, -6, 16, 2, -10, -6, 30, -28, 16; -1, -2, -4, 0, 2, -6, -12, 16, -22, 12, 10, 6, 10, 30, -16, 12; -1, 0, -2, -2, -4, 4, 10, 22, -28, 22, 32, -20, 32, 4, -10, 22; 1, 0, -2, 2, -4, 4, 14, 26, -28, 18, 32, -20, 32, 4, -6, 18] 8 ![1, 1, 2, 2, 4, 4, 8, 16]) := by smith

#print axioms result
