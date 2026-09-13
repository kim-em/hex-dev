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

theorem result : minpoly ℚ (!![0, 369620939, 0, 0, 0, 0, 0, 0; 0, 0, 910232781, 0, 0, 0, 0, 0; 0, 0, 0, 1454372225, 0, 0, 0, 0; 0, 0, 0, 0, 1878802002, 0, 0, 0; 0, 0, 0, 0, 0, 1771024359, 0, 0; 0, 0, 0, 0, 0, 0, 63983012, 0; 0, 0, 0, 0, 0, 0, 0, 1738747071; 0, 0, 0, 0, 0, 0, 0, 0] : Matrix (Fin 8) (Fin 8) ℚ) =
    Polynomial.X ^ 8 := by min_poly

#print axioms result
