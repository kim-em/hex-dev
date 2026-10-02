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

theorem result : minpoly ℚ (!![0, 0, 0, -813035161, 0, 0, 0, 0; 1, 0, 0, 1033899433, 0, 0, 0, 0; 0, 1, 0, 499475046, 0, 0, 0, 0; 0, 0, 1, 33418943, 0, 0, 0, 0; 0, 0, 0, 0, 0, 0, 0, -813035161; 0, 0, 0, 0, 1, 0, 0, 1033899433; 0, 0, 0, 0, 0, 1, 0, 499475046; 0, 0, 0, 0, 0, 0, 1, 33418943] : Matrix (Fin 8) (Fin 8) ℚ) =
    Polynomial.C 813035161 + Polynomial.C (-1033899433) * Polynomial.X + Polynomial.C (-499475046) * Polynomial.X ^ 2 + Polynomial.C (-33418943) * Polynomial.X ^ 3 + Polynomial.X ^ 4 := by min_poly

#print axioms result
