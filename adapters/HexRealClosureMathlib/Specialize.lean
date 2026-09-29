/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexOrderedFnMathlib.Infinitesimal
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Instances.Sign

public section

namespace Hex.RealClosure.Specialize
open Polynomial Filter Topology

/-- Near zero on the positive side, a real polynomial has the sign of its
lowest nonzero coefficient. The zero polynomial retains zero sign. -/
theorem polynomial_sign (p : Polynomial ℝ) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), SignType.sign (p.eval t) = SignType.sign p.trailingCoeff := by
  by_cases hp : p = 0
  · simp [hp]
  let q := p /ₘ (X - C 0) ^ p.rootMultiplicity 0
  have nonzero : q.eval 0 ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero 0 hp
  have constant : q.eval 0 = p.trailingCoeff := by
    simpa [q] using (eval_divByMonic_eq_trailingCoeff_comp (p := p) (t := 0))
  have continuous : ContinuousAt (fun t => SignType.sign (q.eval t)) 0 :=
    ContinuousAt.comp (f := fun t : ℝ => q.eval t)
      (continuousAt_sign_of_ne_zero nonzero) q.continuousAt
  have stable : ∀ᶠ t in 𝓝 (0 : ℝ), SignType.sign (q.eval t) = SignType.sign (q.eval 0) :=
    tendsto_pure.mp (by simpa only [nhds_discrete] using continuous.tendsto)
  filter_upwards [stable.filter_mono nhdsWithin_le_nhds, eventually_mem_nhdsWithin] with t sign positive
  have factor : p.eval t = t ^ p.rootMultiplicity 0 * q.eval t := by
    simpa only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, sub_zero, q] using
      (congrArg (fun f : Polynomial ℝ => f.eval t) (p.pow_mul_divByMonic_rootMultiplicity_eq 0)).symm
  rw [factor, sign_mul, sign_pos (pow_pos positive _), one_mul, sign, constant]

/-- One positive neighborhood preserves every sign in a finite polynomial family. -/
theorem finite_signs (polynomials : Finset (Polynomial ℝ)) :
    ∃ η > (0 : ℝ), ∀ t, 0 < t → t < η → ∀ p ∈ polynomials,
      SignType.sign (p.eval t) = SignType.sign p.trailingCoeff := by
  have stable : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ p ∈ polynomials,
      SignType.sign (p.eval t) = SignType.sign p.trailingCoeff :=
    (eventually_all_finset polynomials).mpr fun p _ => polynomial_sign p
  obtain ⟨η, positive, holds⟩ := Metric.mem_nhdsWithin_iff.mp stable
  refine ⟨η, positive, fun t ht hη => holds ?_⟩
  exact ⟨by simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ht] using hη, ht⟩

/-- A single ordinary real parameter realizes all these signs below any
prescribed positive cap, retaining strict sector inequalities. -/
theorem exists_parameter (polynomials : Finset (Polynomial ℝ)) (cap : ℝ) (positive : 0 < cap) :
    ∃ t : ℝ, 0 < t ∧ t < cap ∧ ∀ p ∈ polynomials,
      SignType.sign (p.eval t) = SignType.sign p.trailingCoeff := by
  obtain ⟨η, hη, signs⟩ := finite_signs polynomials
  let t := min η cap / 2
  have hp : 0 < min η cap := lt_min hη positive
  have belowη : t < η := by dsimp [t]; linarith [min_le_left η cap]
  have belowcap : t < cap := by dsimp [t]; linarith [min_le_right η cap]
  have ht : 0 < t := by dsimp [t]; positivity
  exact ⟨t, ht, belowcap, signs t ht belowη⟩

section Fractions
attribute [local instance 2000] Field.toGrindField

/-- Evaluate the stored numerator and denominator at one ordinary real parameter.
The denominator guard is proved locally; this is not a field hom on all fractions. -/
@[expose] noncomputable def evalFraction (f : Hex.RationalFn ℝ) (t : ℝ) : ℝ :=
  (HexPolyMathlib.toPolynomial f.num).eval t / (HexPolyMathlib.toPolynomial f.den).eval t

/-- Actual native lowest-coefficient signs agree with real evaluation near zero. -/
theorem native_polynomial_sign (p : Hex.DensePoly ℝ) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), SignType.sign ((HexPolyMathlib.toPolynomial p).eval t) =
      SignType.sign (Hex.OrderedFn.Infinitesimal.lowestCoeff p) := by
  rw [Hex.OrderedFn.Infinitesimal.lowestCoeff_eq]
  exact polynomial_sign _

/-- Every stored canonical fraction has one neighborhood preserving its actual
infinitesimal sign and the nonzero denominator needed for specialization. -/
theorem fraction_sign (f : Hex.RationalFn ℝ) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (HexPolyMathlib.toPolynomial f.den).eval t ≠ 0 ∧
      (SignType.sign (evalFraction f t) : Int) =
        Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign f := by
  have nonzero : HexPolyMathlib.toPolynomial f.den ≠ 0 := by
    intro zero
    apply f.den_ne_zero
    apply Hex.DensePoly.ext_coeff
    intro i
    have equal := congrArg (fun p : Polynomial ℝ => p.coeff i) zero
    simpa only [HexPolyMathlib.coeff_toPolynomial, Polynomial.coeff_zero,
      Hex.DensePoly.coeff_zero] using equal
  have lowest : Hex.OrderedFn.Infinitesimal.lowestCoeff f.den ≠ 0 := by
    rw [Hex.OrderedFn.Infinitesimal.lowestCoeff_eq]
    exact trailingCoeff_nonzero_iff_nonzero.mpr nonzero
  filter_upwards [native_polynomial_sign f.num, native_polynomial_sign f.den] with t numerator denominator
  have guard : (HexPolyMathlib.toPolynomial f.den).eval t ≠ 0 := by
    intro zero
    rw [zero, sign_zero] at denominator
    exact lowest (sign_eq_zero_iff.mp denominator.symm)
  refine ⟨guard, ?_⟩
  by_cases zero : f.num = 0
  · simp [evalFraction, zero, HexPolyMathlib.toPolynomial_zero, Hex.OrderedFn.Infinitesimal.sign]
  · rw [Hex.OrderedFn.Infinitesimal.sign, ite_eq_right zero,
      Hex.OrderedFn.Infinitesimal.orderSign_eq, Hex.OrderedFn.Infinitesimal.orderSign_eq]
    have inverse (x : ℝ) : SignType.sign x⁻¹ = SignType.sign x := by
      simp only [sign_apply, inv_pos, inv_lt_zero]
    simp only [evalFraction, div_eq_mul_inv, sign_mul, inverse, numerator,
      denominator, SignType.coe_mul]
/-- All fractions in finite recorded data share one neighborhood preserving
native signs and every denominator guard simultaneously. -/
theorem finite_fractions (fractions : Finset (Hex.RationalFn ℝ)) :
    ∃ η > (0 : ℝ), ∀ t, 0 < t → t < η → ∀ f ∈ fractions,
      (HexPolyMathlib.toPolynomial f.den).eval t ≠ 0 ∧
      (SignType.sign (evalFraction f t) : Int) =
        Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign f := by
  have stable : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ f ∈ fractions,
      (HexPolyMathlib.toPolynomial f.den).eval t ≠ 0 ∧
      (SignType.sign (evalFraction f t) : Int) =
        Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign f :=
    (eventually_all_finset fractions).mpr fun f _ => fraction_sign f
  obtain ⟨η, positive, holds⟩ := Metric.mem_nhdsWithin_iff.mp stable
  refine ⟨η, positive, fun t ht hη => holds ?_⟩
  exact ⟨by simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ht] using hη, ht⟩

/-- One ordinary real parameter below a positive cap preserves all signs and
denominator guards of the finite native fraction data together. -/
theorem exists_fraction_parameter (fractions : Finset (Hex.RationalFn ℝ))
    (cap : ℝ) (positive : 0 < cap) :
    ∃ t : ℝ, 0 < t ∧ t < cap ∧ ∀ f ∈ fractions,
      (HexPolyMathlib.toPolynomial f.den).eval t ≠ 0 ∧
      (SignType.sign (evalFraction f t) : Int) =
        Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign f := by
  obtain ⟨η, hη, signs⟩ := finite_fractions fractions
  let t := min η cap / 2
  have hp : 0 < min η cap := lt_min hη positive
  have belowη : t < η := by dsimp [t]; linarith [min_le_left η cap]
  have belowcap : t < cap := by dsimp [t]; linarith [min_le_right η cap]
  have ht : 0 < t := by dsimp [t]; positivity
  exact ⟨t, ht, belowcap, signs t ht belowη⟩

end Fractions

end Hex.RealClosure.Specialize

/-- info: 'Hex.RealClosure.Specialize.polynomial_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.polynomial_sign

/-- info: 'Hex.RealClosure.Specialize.exists_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.exists_parameter

/-- info: 'Hex.RealClosure.Specialize.fraction_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.fraction_sign

/-- info: 'Hex.RealClosure.Specialize.exists_fraction_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.exists_fraction_parameter
