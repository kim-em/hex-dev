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

theorem result : minpoly ℚ (!![(40 / 43), (-85 / 129), (10 / 43), (-112 / 129), (62 / 129), (-42 / 43), (112 / 129), (2 / 129); (16 / 43), (-27 / 43), (-97 / 129), (9 / 43), (-4 / 129), (46 / 129), (24 / 43), (-31 / 43); (65 / 129), (-29 / 129), (-10 / 129), (-109 / 129), (-30 / 43), (112 / 129), (17 / 43), (8 / 43); (-94 / 129), (-53 / 129), (44 / 129), (17 / 43), (1 / 3), (70 / 129), (-17 / 43), (104 / 129); (41 / 43), (56 / 129), (-9 / 43), (-35 / 43), (122 / 129), (-128 / 129), (94 / 129), (116 / 129); (-67 / 129), (-16 / 129), (-31 / 129), (-39 / 43), (-50 / 129), (-40 / 43), (64 / 129), (118 / 129); (-26 / 43), (100 / 129), 0, (79 / 129), (36 / 43), (-83 / 129), (15 / 43), (-34 / 43); (31 / 43), (97 / 129), (2 / 3), (17 / 129), (-76 / 129), (28 / 129), (8 / 129), (-52 / 129)] : Matrix (Fin 8) (Fin 8) ℚ) =
    Polynomial.C (451070109725558000 / 76686282021340161) + Polynomial.C (-5328042402529334 / 594467302491009) * Polynomial.X + Polynomial.C (46934641282232 / 4608273662721) * Polynomial.X ^ 2 + Polynomial.C (-50068890139 / 3969227961) * Polynomial.X ^ 3 + Polynomial.C (9694391 / 6440067) * Polynomial.X ^ 4 + Polynomial.C (-6942946 / 2146689) * Polynomial.X ^ 5 + Polynomial.C (-26714 / 16641) * Polynomial.X ^ 6 + Polynomial.C (-25 / 43) * Polynomial.X ^ 7 + Polynomial.X ^ 8 := by min_poly

#print axioms result
