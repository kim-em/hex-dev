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

theorem result : Nonempty (HexHermiteMathlib.HermiteBasis !![2, 2, -2, -2, 2, -2, 2, -2; 2, 18, 14, 14, -14, -18, -14, 14; -2, 14, 274, 274, -274, 242, -274, 274; -2, 14, -238, 3858, 4334, -4366, 4334, -4334; 2, 18, 270, 4366, 69362, 61678, 69362, 61710; 2, -14, 238, 4334, 69394, 1110286, -979182, -986898; 2, 18, 270, 4366, 69362, 1110254, 15798002, -17764082; -2, -18, 242, 4338, 69390, 1110290, 15798030, 250671346; 2, 18, 270, -3826, 61170, 1118446, 15789810, -286191346; 2, -14, 238, 4334, 69394, 1110286, -17756398, 284225774; 2, -14, 238, 4334, -61678, -1117938, -15790318, -250679058; -2, 14, 274, 4370, -61714, 979186, 15666926, 250540306; -2, -18, 242, -3854, 61198, -978670, 17886990, 252776690; -2, 14, -238, 3858, 69870, -987406, 17895662, 252768018; -2, 14, 274, -3822, -69906, 987378, -17895698, -252767982; -2, 14, -238, -4334, -69394, 986866, -17895186, -252768494] 8) := by hermite

#print axioms result
