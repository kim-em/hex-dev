/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultantMathlib.Sylvester

public section

/-!
Agreement of the executable discriminant with Mathlib.
-/
namespace Hex.DensePoly

universe u

variable {R : Type u}

/-- The executable and Mathlib discriminants agree under dense-polynomial
correspondence. -/
theorem toPolynomial_disc [CommRing R] [IsDomain R] [DecidableEq R]
    [Div R] [Hex.ExactDivLaws R] (f : DensePoly R) :
    disc f = Polynomial.discr (HexPolyMathlib.toPolynomial f) := by
  sorry

end Hex.DensePoly
