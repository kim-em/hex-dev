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

theorem result : (![0, 1073741824, -1073741824, -1073741824] : Fin 4 → ℤ) ∈
    Submodule.span ℤ (Set.range !![2, 2, -2, 2; 2, 1073741826, -1073741826, -1073741822; -2, -1073741826, 1073741826, 1073741822; -2, -1073741826, 1073741826, 1073741822]) := by hermite

#print axioms result
