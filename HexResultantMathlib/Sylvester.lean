/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultantMathlib.Basic

public section

/-!
Full-value correspondence between Brown's executable recurrence and Mathlib's
Sylvester-determinant resultant.
-/
namespace Hex.DensePoly

universe u

variable {R : Type u}

/-- The executable and Mathlib resultants agree under dense-polynomial
correspondence, with the executable default formal degrees made explicit. -/
theorem toPolynomial_resultant [CommRing R] [IsDomain R] [DecidableEq R]
    [Div R] [Hex.ExactDivLaws R] (f g : DensePoly R) :
    resultant f g =
      Polynomial.resultant (HexPolyMathlib.toPolynomial f)
        (HexPolyMathlib.toPolynomial g)
        (m := f.degree?.getD 0) (n := g.degree?.getD 0) := by
  sorry

end Hex.DensePoly
