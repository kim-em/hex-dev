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

theorem result : minpoly ℚ (!![-1580120956, 0; 0, -1580120956] : Matrix (Fin 2) (Fin 2) ℚ) =
    Polynomial.C 1580120956 + Polynomial.X := by min_poly

#print axioms result
