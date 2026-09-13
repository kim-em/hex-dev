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

theorem result : Nonempty (HexHermiteMathlib.HermiteBasis !![2, 2, 2, 2, -2, -2, 2, 2; -2, 1022, 1022, -1026, 1026, -1022, 1022, 1022; -2, -1026, 523262, -523266, -525310, -523262, 523262, -525314; -2, -1026, -525314, 537396222, -536347646, 537396226, 536345598, -536347650; 2, -1022, 523266, 536347650, -537396226, 536347646, 537394178, -537396222; 2, -1022, 523266, 536347650, -537396226, 536347646, 537394178, -537396222; 2, 1026, 525314, 536345602, -537394178, 536345598, 537396226, -537394174; -2, -1026, -525314, -536345602, 537394178, -536345598, -537396226, 537394174] 4) := by hermite

#print axioms result
