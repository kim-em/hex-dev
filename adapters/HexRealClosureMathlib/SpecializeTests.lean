/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.Specialize
public import Mathlib.Analysis.Real.Sqrt

public section

namespace Hex.RealClosure.Specialize.Tests
attribute [local instance 2000] Field.toGrindField

/-- The same ordinary parameter satisfies all fraction signs and denominator
guards together with the square-root equation and strict infinitesimal inequalities. -/
example (fractions : Finset (Hex.RationalFn ℝ)) :
    ∃ t s : ℝ, 0 < t ∧ t < 1 ∧ 0 < s ∧ s ^ 2 = t ∧ t < s ∧ s < 1 ∧
      ∀ f ∈ fractions, (HexPolyMathlib.toPolynomial f.den).eval t ≠ 0 ∧
        (SignType.sign (evalFraction f t) : Int) =
          Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign f := by
  obtain ⟨t, positive, small, signs⟩ := exists_fraction_parameter fractions 1 zero_lt_one
  have square : (Real.sqrt t) ^ 2 = t := Real.sq_sqrt positive.le
  have nonnegative : 0 ≤ Real.sqrt t := Real.sqrt_nonneg t
  have root_positive : 0 < Real.sqrt t := Real.sqrt_pos.mpr positive
  refine ⟨t, Real.sqrt t, positive, small, root_positive, square, ?_, ?_, signs⟩
  · nlinarith
  · nlinarith

/-- Zero polynomials retain zero sign in the same finite-family realization. -/
example (polynomials : Finset (Polynomial ℝ)) (cap : ℝ) (positive : 0 < cap) :
    ∃ t : ℝ, 0 < t ∧ t < cap ∧ (SignType.sign ((0 : Polynomial ℝ).eval t) : Int) = 0 ∧
      ∀ p ∈ polynomials, SignType.sign (p.eval t) = SignType.sign p.trailingCoeff := by
  obtain ⟨t, ht, hc, signs⟩ := exists_parameter polynomials cap positive
  exact ⟨t, ht, hc, by simp, signs⟩

end Hex.RealClosure.Specialize.Tests
