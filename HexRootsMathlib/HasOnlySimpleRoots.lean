/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRoots.Basic
public import HexPolyZMathlib.Squarefree

public section

/-!
# Semantics of `Hex.HasOnlySimpleRoots`

The executable predicate computes a rational polynomial gcd, so its faithful
Mathlib interpretation is squarefreeness (or separability) after mapping to
`ℚ[X]`. It is not integral-polynomial squarefreeness, which additionally sees
square factors in the integer content.
-/

open Polynomial

namespace HexRootsMathlib

/-- On nonzero inputs, the executable simple-root predicate is exactly
squarefreeness of the rational cast. -/
theorem hasOnlySimpleRoots_iff_squarefree (p : Hex.ZPoly) (hp : p ≠ 0) :
    Hex.HasOnlySimpleRoots p ↔ Squarefree (HexPolyZMathlib.toPolyℚ p) := by
  change Hex.ZPoly.SquareFreeRat p ↔ _
  exact HexPolyZMathlib.squareFreeRat_iff p hp

/-- Equivalent separability form of the executable simple-root predicate. -/
theorem hasOnlySimpleRoots_iff_separable (p : Hex.ZPoly) (hp : p ≠ 0) :
    Hex.HasOnlySimpleRoots p ↔ (HexPolyZMathlib.toPolyℚ p).Separable :=
  (hasOnlySimpleRoots_iff_squarefree p hp).trans
    PerfectField.separable_iff_squarefree.symm

/-- A nonzero executable polynomial with only simple roots has separable
rational cast. -/
theorem HasOnlySimpleRoots.separable {p : Hex.ZPoly} (h : Hex.HasOnlySimpleRoots p)
    (hp : p ≠ 0) : (HexPolyZMathlib.toPolyℚ p).Separable :=
  (hasOnlySimpleRoots_iff_separable p hp).mp h

end HexRootsMathlib
