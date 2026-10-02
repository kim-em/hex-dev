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

theorem result : minpoly ℚ (!![(-59 / 129), (-55 / 129); (-5 / 43), (-91 / 129)] : Matrix (Fin 2) (Fin 2) ℚ) =
    Polynomial.C (4544 / 16641) + Polynomial.C (50 / 43) * Polynomial.X + Polynomial.X ^ 2 := by min_poly

#print axioms result
