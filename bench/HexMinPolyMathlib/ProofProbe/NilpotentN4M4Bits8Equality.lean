/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexMinPolyMathlib.Tactic

set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option profiler true
set_option profiler.threshold 1000000
set_option trace.HexMatrix.certificate true

theorem result : minpoly ℚ (!![0, 60, 0, 0; 0, 0, 108, 0; 0, 0, 0, 76; 0, 0, 0, 0] : Matrix (Fin 4) (Fin 4) ℚ) =
    Polynomial.X ^ 4 := by min_poly

#print axioms result
