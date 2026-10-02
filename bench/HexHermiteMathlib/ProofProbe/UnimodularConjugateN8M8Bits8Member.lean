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

theorem result : (![-40, -36, 36, -38, -46, -42, 42, 82] : Fin 8 → ℤ) ∈
    Submodule.span ℤ (Set.range !![16, 14, -14, 16, 16, 20, -20, -28; -14, -12, 14, -16, -16, -20, 20, 28; -14, -14, 16, -16, -16, -20, 20, 28; -12, -12, 12, -10, -14, -18, 18, 26; 12, 12, -12, 14, 18, 18, -18, -26; -8, -8, 8, -10, -10, -6, 14, 22; -8, -8, 8, -10, -10, -14, 22, 22; 0, 0, 0, 2, 2, 6, -6, 2]) := by hermite

#print axioms result
