/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultantMathlib.Sylvester
public import Mathlib.Algebra.Polynomial.Splits

public section

/-!
Root-product form of the Mathlib resultant, retaining root multiplicity.
-/
namespace Hex.DensePoly

universe u

/-- The resultant as the leading-coefficient power times evaluation over all
roots of the first polynomial, counted with multiplicity. -/
theorem resultant_eq_leadingCoeff_mul_prod_roots
    {K : Type u} [Field K] [IsAlgClosed K] (f g : Polynomial K) :
    Polynomial.resultant f g =
      f.leadingCoeff ^ g.natDegree * (f.roots.map g.eval).prod := by
  sorry

end Hex.DensePoly
