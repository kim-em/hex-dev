/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexHermiteTheory.Tactic

set_option maxRecDepth 100000

theorem result : (![-4, -3] : Fin 2 → ℤ) ∉
    Submodule.span ℤ (Set.range !![2, 2; -2, -2]) := by hermite

/-- info: 'result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result
