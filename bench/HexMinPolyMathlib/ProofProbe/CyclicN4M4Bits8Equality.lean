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

theorem result : minpoly ℚ (!![0, 0, 0, 87; 1, 0, 0, 125; 0, 1, 0, 24; 0, 0, 1, -105] : Matrix (Fin 4) (Fin 4) ℚ) =
    Polynomial.C (-87) + Polynomial.C (-125) * Polynomial.X + Polynomial.C (-24) * Polynomial.X ^ 2 + Polynomial.C 105 * Polynomial.X ^ 3 + Polynomial.X ^ 4 := by min_poly

#print axioms result
