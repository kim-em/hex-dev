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

theorem result : (![0, 2, 2, -6, -10, 22, 22, -6] : Fin 8 → ℤ) ∈
    Submodule.span ℤ (Set.range !![2, 2, -2, 2, 2, -2, -2, 2; -2, 0, 0, 0, -4, 0, 0, 0; 2, 4, -2, 2, -2, -6, -2, 6; 2, 0, 2, 2, 6, -6, 6, 6; 2, 0, 2, 2, 10, -10, 10, 2; 2, 4, -2, 6, -2, 2, 6, 6; -2, 0, -2, 6, -2, -6, -2, 6; 2, 4, -2, -2, -2, 2, 14, -2]) := by hermite

#print axioms result
