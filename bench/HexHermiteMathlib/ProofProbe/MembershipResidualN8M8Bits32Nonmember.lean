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

theorem result : (![-12, -1012, -1047540, 535821300, -535821324, -537918452, -537920524, -535823347] : Fin 8 → ℤ) ∉
    Submodule.span ℤ (Set.range !![2, -2, -2, 2, 2, -2, 2, -2; -2, 1026, -1022, 1022, -1026, -1022, 1022, 1026; 2, -1026, 525310, 523266, -523262, 525310, 523266, -525314; -2, -1022, 525314, 537394174, -537394178, -536345598, -536347650, -537396222; 2, 1022, 523262, 537396226, -537396222, -536347650, -536345598, -537394178; 2, -1026, -523266, -537396222, 537396226, 536347646, 536345602, 537394174; 2, 1022, -525314, -537394174, 537394178, 536345598, 536347650, 537396222; -2, 1026, -525310, 536347646, -536347650, -537396222, -537394178, -536345598]) := by hermite

#print axioms result
