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

theorem result : (![536343556, 536346626, 536867842, -1073214466] : Fin 4 → ℤ) ∈
    Submodule.span ℤ (Set.range !![-536345600, -536346624, -536869888, 1073216512; 536344580, 536346626, 536868866, -1073215490; 535821316, 535822338, 536869890, -1072692226; -525308, -524286, -1022, 525310]) := by hermite

#print axioms result
