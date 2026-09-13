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

theorem result : minpoly ℚ (!![0, 0, 0, 0, 0, 0, 0, -23; 1, 0, 0, 0, 0, 0, 0, 86; 0, 1, 0, 0, 0, 0, 0, 5; 0, 0, 1, 0, 0, 0, 0, -85; 0, 0, 0, 1, 0, 0, 0, 29; 0, 0, 0, 0, 1, 0, 0, 34; 0, 0, 0, 0, 0, 1, 0, -89; 0, 0, 0, 0, 0, 0, 1, 103] : Matrix (Fin 8) (Fin 8) ℚ) =
    Polynomial.C 23 + Polynomial.C (-86) * Polynomial.X + Polynomial.C (-5) * Polynomial.X ^ 2 + Polynomial.C 85 * Polynomial.X ^ 3 + Polynomial.C (-29) * Polynomial.X ^ 4 + Polynomial.C (-34) * Polynomial.X ^ 5 + Polynomial.C 89 * Polynomial.X ^ 6 + Polynomial.C (-103) * Polynomial.X ^ 7 + Polynomial.X ^ 8 := by min_poly

#print axioms result
