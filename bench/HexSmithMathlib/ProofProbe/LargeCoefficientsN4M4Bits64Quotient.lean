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

theorem result : Nonempty (HexSmithMathlib.SmithQuotient !![1, 1, -1, 1; 1, 1048577, -1048577, 1048577; 1, 1048577, 1099510579199, -1099510579199; -1, -1048577, -1099510579199, 2305844108724273151] 4 ![1, 1048576, 1099511627776, 2305843009213693952]) := by smith

#print axioms result
