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

theorem result : Nonempty (HexHermiteMathlib.HermiteBasis !![2, -2, -2, 2, -2, -2, -2, -2, -2, 2, 2, -2, 2, 2, 2, 2; -2, 4, 0, -4, 0, 4, 0, 0, 0, -4, 0, 0, 0, 0, -4, 0; -2, 4, 2, -2, -2, 2, -2, -2, 2, -6, -2, -2, 2, 2, -2, 2; -2, 4, -2, -4, 0, 4, 0, 0, -4, 0, 0, 4, -4, 0, -4, -4; -2, 0, 2, -4, 10, 2, 6, 6, 6, 2, 2, 2, -2, -10, -6, -6; -2, 0, 6, 4, -2, 0, 0, 4, 0, 0, -12, 4, -4, 4, 8, -4; -2, 0, 2, 0, 6, -4, 6, -2, 2, 6, -2, 6, -6, -10, -2, -10; -2, 4, 2, -4, 2, 4, -2, 0, 0, -4, -4, -8, 8, -4, -4, 0; 2, 0, -2, 4, -6, -4, -10, -8, -4, 0, 0, -4, 4, 8, 8, -4; 2, 0, -2, 0, -6, 0, -2, 0, 4, -12, 4, 8, -8, 4, -4, 8; -2, 4, -2, -4, -2, 8, -2, 8, -12, 4, -8, 4, -4, 0, -16, -4; -2, 0, 6, 4, -2, -4, 2, 0, 12, -12, 0, 16, -16, 4, 20, 0; 2, 0, -6, -4, -2, 4, 2, 4, -8, 0, -4, 12, -8, -20, -12, 8; -2, 4, -2, -4, -2, 4, 2, 0, 4, -4, 0, 24, -28, 4, 12, 0; -2, 0, 2, -4, 6, 4, 14, 8, 4, -4, -8, 24, -28, -12, 16, -4; 2, -4, -2, 0, 2, 4, 6, 4, -8, 16, -12, -4, 8, -8, -4, 16] 16) := by hermite

#print axioms result
