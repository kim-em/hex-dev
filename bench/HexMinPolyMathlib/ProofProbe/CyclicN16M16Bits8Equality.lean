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

theorem result : minpoly ℚ (!![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 32; 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -59; 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -52; 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -27; 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 16; 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 98; 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -18; 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, -103; 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -47; 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 59; 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -26; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 48; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, -62; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 30; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 114; 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 48] : Matrix (Fin 16) (Fin 16) ℚ) =
    Polynomial.C (-32) + Polynomial.C 59 * Polynomial.X + Polynomial.C 52 * Polynomial.X ^ 2 + Polynomial.C 27 * Polynomial.X ^ 3 + Polynomial.C (-16) * Polynomial.X ^ 4 + Polynomial.C (-98) * Polynomial.X ^ 5 + Polynomial.C 18 * Polynomial.X ^ 6 + Polynomial.C 103 * Polynomial.X ^ 7 + Polynomial.C 47 * Polynomial.X ^ 8 + Polynomial.C (-59) * Polynomial.X ^ 9 + Polynomial.C 26 * Polynomial.X ^ 10 + Polynomial.C (-48) * Polynomial.X ^ 11 + Polynomial.C 62 * Polynomial.X ^ 12 + Polynomial.C (-30) * Polynomial.X ^ 13 + Polynomial.C (-114) * Polynomial.X ^ 14 + Polynomial.C (-48) * Polynomial.X ^ 15 + Polynomial.X ^ 16 := by min_poly

#print axioms result
