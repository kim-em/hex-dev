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

theorem result : (![-4, 16, -16, 16, -48, -40, 24, 17] : Fin 8 → ℤ) ∉
    Submodule.span ℤ (Set.range !![2, -2, 2, 2, 2, -2, -2, 2; -2, 6, -6, -6, -6, -2, -2, -6; 2, -6, 14, 14, -2, 10, 10, -2; 2, -6, 14, 46, -34, -22, 42, 30; 2, -6, -2, 30, -18, -38, 26, 46; -2, -2, -6, 26, -22, -34, 30, 42; -2, -2, -6, 26, -22, -34, 30, 42; 2, 2, -10, 22, -26, -46, 18, 38]) := by hermite

#print axioms result
