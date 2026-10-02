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

theorem result : minpoly ℚ (!![(304350410 / 2147483649), (-1148470102 / 2147483649), (286669224 / 715827883), (-624824554 / 715827883); (-1123569731 / 2147483649), (1547534720 / 2147483649), (-475020696 / 715827883), (-299261318 / 715827883); (568697781 / 715827883), (288786885 / 715827883), (-1850731627 / 2147483649), (74302706 / 715827883); (-634864547 / 715827883), (-299902676 / 2147483649), (399985431 / 715827883), (633761767 / 2147483649)] : Matrix (Fin 4) (Fin 4) ℚ) =
    Polynomial.C (2049783471180591415859912070822657724 / 21267647972172735251263197880411750401) + Polynomial.C (7894749050182932431640052672 / 9903520328118100260917608449) * Polynomial.X + Polynomial.C (-8585478816856244747 / 4611686022722355201) * Polynomial.X ^ 2 + Polynomial.C (-634915270 / 2147483649) * Polynomial.X ^ 3 + Polynomial.X ^ 4 := by min_poly

#print axioms result
