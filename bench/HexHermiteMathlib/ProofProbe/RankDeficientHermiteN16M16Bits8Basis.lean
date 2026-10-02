/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexHermiteMathlib.Tactic

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 1000000
set_option trace.HexMatrix.certificate true

theorem result : Nonempty (HexHermiteMathlib.HermiteBasis !![2, -2, -2, 2, -2, 2, -2, -2, -2, 2, -2, 2, -2, 2, -2, 2; -2, 4, 4, 0, 4, -4, 0, 4, 4, 0, 0, -4, 4, -4, 0, 0; 2, 0, 2, 6, -2, 2, -2, -2, -2, 6, -2, -2, 2, -2, -2, 2; -2, 4, 6, 6, 6, 2, -2, -2, -2, -2, -2, -10, 10, -2, 6, -6; 2, -4, -2, 6, 2, 14, 2, -6, -14, 2, -6, -6, 6, 2, 10, -2; -2, 4, 2, -6, -2, -6, 6, 14, 6, 6, 14, 14, -14, 6, -18, -6; 2, -4, -6, 2, -2, 10, 6, 6, -18, 6, -2, 22, -6, 30, -18, -6; 2, 0, -2, -2, -6, -18, -22, 2, 42, 2, 18, -22, 6, 2, -14, 22; -2, 4, 6, 6, 2, -10, -6, 10, 18, 10, 2, -22, 38, 18, -14, 22; 2, 0, 2, 10, 6, 2, -18, -34, -10, -26, -26, -10, -6, -34, 38, -14; -2, 0, 2, 2, -2, -6, -18, -42, -2, -42, -10, -2, -14, -26, 38, -30; -2, 0, 2, 2, 6, 2, -10, -34, -10, -34, -18, -10, -6, -34, 46, -22; 2, 0, -2, 6, 10, -2, -6, -14, -22, -14, -46, 10, 6, -14, 18, 6; -2, 4, 6, 6, 10, -2, -14, 2, 26, 2, 10, -46, 30, -6, 10, 14; 2, -4, -2, -2, -6, -2, -6, 2, 26, 10, 18, -30, 14, -6, 2, 22; 2, 0, 2, 2, -10, -14, -18, -34, 6, -26, -10, 6, -22, -34, 22, -14] 8) := by hermite

#print axioms result
