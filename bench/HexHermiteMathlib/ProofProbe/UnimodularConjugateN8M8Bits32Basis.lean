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

theorem result : Nonempty (HexHermiteMathlib.HermiteBasis !![2, 2, -2, 2, 2, 2, -2, 2; 2, 18, -18, 18, -14, 18, 14, -14; -2, 14, 242, 270, -274, -242, 274, 238; 2, -14, -242, 3826, -3822, -3854, 3822, 3858; -2, -18, -238, -4370, 69902, -61202, -69902, -69874; -2, -18, -238, 3822, -69362, 1110254, 1117938, -979186; -2, 14, -270, 3854, -69394, 1110286, 17895186, -17756434; -2, -18, -238, -4370, -61170, -978706, 15789810, 252768014] 8) := by hermite

#print axioms result
