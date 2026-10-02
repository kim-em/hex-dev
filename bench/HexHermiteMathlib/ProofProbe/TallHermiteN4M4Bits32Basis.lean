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

theorem result : Nonempty (HexHermiteMathlib.HermiteBasis !![2, -2, 2, -2; 2, 1022, 1026, -1026; -2, 1026, 525310, 523266; 2, -1026, 523266, 537396222; 2, -1026, -525310, 536347646; -2, -1022, -525314, 536347650; -2, -1022, 523262, 537396226; 2, -1026, -525310, -537394178] 4) := by hermite

#print axioms result
