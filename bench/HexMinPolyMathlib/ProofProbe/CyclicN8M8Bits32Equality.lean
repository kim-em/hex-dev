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

theorem result : minpoly ℚ (!![0, 0, 0, 0, 0, 0, 0, -1999327548; 1, 0, 0, 0, 0, 0, 0, -1139715519; 0, 1, 0, 0, 0, 0, 0, -1727525417; 0, 0, 1, 0, 0, 0, 0, 923184497; 0, 0, 0, 1, 0, 0, 0, 663467466; 0, 0, 0, 0, 1, 0, 0, -781159453; 0, 0, 0, 0, 0, 1, 0, -394904373; 0, 0, 0, 0, 0, 0, 1, -866828206] : Matrix (Fin 8) (Fin 8) ℚ) =
    Polynomial.C 1999327548 + Polynomial.C 1139715519 * Polynomial.X + Polynomial.C 1727525417 * Polynomial.X ^ 2 + Polynomial.C (-923184497) * Polynomial.X ^ 3 + Polynomial.C (-663467466) * Polynomial.X ^ 4 + Polynomial.C 781159453 * Polynomial.X ^ 5 + Polynomial.C 394904373 * Polynomial.X ^ 6 + Polynomial.C 866828206 * Polynomial.X ^ 7 + Polynomial.X ^ 8 := by min_poly

#print axioms result
