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

theorem result : minpoly ℚ (!![(22 / 43), (-124 / 129), (34 / 129), (-89 / 129); (-25 / 129), (-13 / 129), (119 / 129), (44 / 129); (-56 / 129), (56 / 129), 0, (-2 / 43); (55 / 129), (41 / 43), (27 / 43), (-27 / 43)] : Matrix (Fin 4) (Fin 4) ℚ) =
    Polynomial.C (-61972520 / 92307627) + Polynomial.C (-1103090 / 2146689) * Polynomial.X + Polynomial.C (-13042 / 16641) * Polynomial.X ^ 2 + Polynomial.C (28 / 129) * Polynomial.X ^ 3 + Polynomial.X ^ 4 := by min_poly

#print axioms result
