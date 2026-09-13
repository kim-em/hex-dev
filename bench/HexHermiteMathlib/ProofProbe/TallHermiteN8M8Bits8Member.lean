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

theorem result : (![0, 2, 2, 6, -14, 10, -10, 66] : Fin 8 → ℤ) ∈
    Submodule.span ℤ (Set.range !![2, -2, -2, 2, 2, -2, -2, -2; -2, 4, 0, -4, 0, 4, 0, 4; -2, 4, 2, -6, 2, 2, 2, 6; -2, 4, 2, -2, -2, 6, -2, 10; -2, 4, -2, -6, 6, 6, -2, 2; -2, 4, -2, -6, -2, 6, 14, -14; -2, 4, -2, 2, -2, 6, -10, 26; 2, -4, 2, 6, -6, 2, 18, 14; 2, 0, -2, -6, 6, -18, -10, -22; 2, 0, -2, -6, 14, -10, -18, -14; -2, 0, 2, -2, -6, 2, 26, -26; -2, 0, 2, -2, 2, -6, -14, 14; -2, 0, 2, 6, -6, 18, 10, 22; 2, 0, -6, 6, -6, -6, -6, 30; 2, 0, -6, -2, 10, -6, -6, -2; -2, 4, -2, 2, -2, 22, 6, 26]) := by hermite

#print axioms result
