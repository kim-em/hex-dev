/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexMinPolyMathlib.Tactic

set_option maxRecDepth 100000

theorem result : minpoly ℚ (!![0, -117; 1, 112] : Matrix (Fin 2) (Fin 2) ℚ) =
    Polynomial.C 117 + Polynomial.C (-112) * Polynomial.X + Polynomial.X ^ 2 := by min_poly

/-- info: 'result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result
