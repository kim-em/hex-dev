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

theorem result : Nonempty (HexHermiteMathlib.HermiteBasis !![2, 2, -2, 2, -2, -2, 2, -2; 2, 6, -6, 6, 2, 2, 6, 2; -2, 2, 6, 10, -2, 14, -6, 14; 2, 6, 2, 46, -38, -22, -34, 42; -2, 2, 6, -22, 30, 46, 26, -18; -2, -6, -2, 18, -26, -42, -30, 22; 2, 6, -14, 30, -22, -38, -18, 26; -2, 2, 6, -22, 30, 46, 26, -18] 4) := by hermite

#print axioms result
