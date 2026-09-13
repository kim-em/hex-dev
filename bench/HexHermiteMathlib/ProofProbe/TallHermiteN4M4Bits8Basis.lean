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

theorem result : Nonempty (HexHermiteMathlib.HermiteBasis !![2, 2, 2, -2; 2, 6, -2, -6; -2, 2, 2, -10; -2, -6, 10, 30; 2, 6, -10, 34; -2, 2, -14, -26; -2, -6, -6, -18; -2, 2, -14, -26] 4) := by hermite

#print axioms result
