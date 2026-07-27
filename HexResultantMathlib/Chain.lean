/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultantMathlib.Basic

public section

/-!
Common-root consequences of the executable subresultant chain.
-/
namespace Hex.DensePoly

/-- Two nonzero integer dense polynomials have zero executable resultant
exactly when they share a complex root. -/
theorem resultant_eq_zero_iff_common_root
    (f g : DensePoly Int) (hf : f ≠ 0) (hg : g ≠ 0) :
    resultant f g = 0 ↔
      ∃ z : ℂ,
        Polynomial.aeval z (HexPolyMathlib.toPolynomial f) = 0 ∧
        Polynomial.aeval z (HexPolyMathlib.toPolynomial g) = 0 := by
  sorry

end Hex.DensePoly
