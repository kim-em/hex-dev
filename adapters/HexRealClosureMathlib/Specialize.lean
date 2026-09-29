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

section Embedded
variable {F : Type u} [Field F]

private theorem trailing_map (embedding : F →+* ℝ) (p : Polynomial F) :
    (p.map embedding).trailingCoeff = embedding p.trailingCoeff := by
  by_cases zero : p = 0
  · simp [zero]
  have mapped : p.map embedding ≠ 0 := by
    intro h
    apply zero
    apply Polynomial.ext
    intro i
    have coefficient := congrArg (fun q : Polynomial ℝ => q.coeff i) h
    exact embedding.injective (by simpa using coefficient)
  have degree : (p.map embedding).natTrailingDegree = p.natTrailingDegree := by
    apply Nat.le_antisymm
    · apply natTrailingDegree_le_of_ne_zero
      rw [Polynomial.coeff_map]
      exact fun h => (coeff_natTrailingDegree_ne_zero.mpr zero)
        (embedding.injective (h.trans embedding.map_zero.symm))
    · apply natTrailingDegree_le_of_ne_zero
      intro h
      have coefficient := coeff_natTrailingDegree_ne_zero.mpr mapped
      apply coefficient
      rw [Polynomial.coeff_map, h, embedding.map_zero]
  simp only [Polynomial.trailingCoeff, degree, Polynomial.coeff_map]

variable [LinearOrder F]

/-- An ordered coefficient embedding preserves the actual near-zero sign. -/
theorem polynomial_sign_map (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (p : Polynomial F) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      SignType.sign ((p.map embedding).eval t) = SignType.sign p.trailingCoeff := by
  have stable := polynomial_sign (p.map embedding)
  simpa only [trailing_map, ordered.sign_comp] using stable

end Embedded

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

section EmbeddedFractions
variable {F : Type} [Field F] [DecidableEq F]

/-- Evaluate actual native fraction coefficients through the prescribed embedding. -/
@[expose] noncomputable def evalMapped (embedding : F →+* ℝ)
    (fraction : Hex.RationalFn F) (t : ℝ) : ℝ :=
  ((HexPolyMathlib.toPolynomial fraction.num).map embedding).eval t /
    ((HexPolyMathlib.toPolynomial fraction.den).map embedding).eval t

/-- Specialization preserves an actual native sum wherever the finitely
recorded denominators of both operands and their result are nonzero. -/
theorem evalMapped_add (embedding : F →+* ℝ) (first second : Hex.RationalFn F) (t : ℝ)
    (left : ((HexPolyMathlib.toPolynomial first.den).map embedding).eval t ≠ 0)
    (right : ((HexPolyMathlib.toPolynomial second.den).map embedding).eval t ≠ 0)
    (result : ((HexPolyMathlib.toPolynomial (first + second).den).map embedding).eval t ≠ 0) :
    evalMapped embedding (first + second) t =
      evalMapped embedding first t + evalMapped embedding second t := by
  have identity := congrArg (fun p : Hex.DensePoly F =>
    ((HexPolyMathlib.toPolynomial p).map embedding).eval t) (Hex.RationalFn.add_spec first second)
  simp only [HexPolyMathlib.toPolynomial_mul, HexPolyMathlib.toPolynomial_add,
    Polynomial.map_mul, Polynomial.map_add, Polynomial.eval_mul, Polynomial.eval_add] at identity
  unfold evalMapped
  field_simp [left, right, result]
  nlinarith only [identity]

/-- Specialization preserves an actual native product on its recorded
nonzero denominator guards, without a global field-hom assumption. -/
theorem evalMapped_mul (embedding : F →+* ℝ) (first second : Hex.RationalFn F) (t : ℝ)
    (left : ((HexPolyMathlib.toPolynomial first.den).map embedding).eval t ≠ 0)
    (right : ((HexPolyMathlib.toPolynomial second.den).map embedding).eval t ≠ 0)
    (result : ((HexPolyMathlib.toPolynomial (first * second).den).map embedding).eval t ≠ 0) :
    evalMapped embedding (first * second) t =
      evalMapped embedding first t * evalMapped embedding second t := by
  have identity := congrArg (fun p : Hex.DensePoly F =>
    ((HexPolyMathlib.toPolynomial p).map embedding).eval t) (Hex.RationalFn.mul_spec first second)
  simp only [HexPolyMathlib.toPolynomial_mul, Polynomial.map_mul, Polynomial.eval_mul] at identity
  unfold evalMapped
  field_simp [left, right, result]
  nlinarith only [identity]

variable [LinearOrder F]

/-- Ordered coefficient embeddings preserve each native fraction's infinitesimal
sign on one positive neighborhood, including its actual denominator guard. -/
theorem fraction_sign_map (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (fraction : Hex.RationalFn F) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ((HexPolyMathlib.toPolynomial fraction.den).map embedding).eval t ≠ 0 ∧
      (SignType.sign (evalMapped embedding fraction t) : Int) =
        Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign fraction := by
  have nonzero : HexPolyMathlib.toPolynomial fraction.den ≠ 0 := by
    intro zero
    apply fraction.den_ne_zero
    apply Hex.DensePoly.ext_coeff
    intro i
    have equal := congrArg (fun p : Polynomial F => p.coeff i) zero
    simpa only [HexPolyMathlib.coeff_toPolynomial, Polynomial.coeff_zero,
      Hex.DensePoly.coeff_zero] using equal
  have lowest : (HexPolyMathlib.toPolynomial fraction.den).trailingCoeff ≠ 0 :=
    trailingCoeff_nonzero_iff_nonzero.mpr nonzero
  filter_upwards [polynomial_sign_map embedding ordered (HexPolyMathlib.toPolynomial fraction.num),
    polynomial_sign_map embedding ordered (HexPolyMathlib.toPolynomial fraction.den)] with t numerator denominator
  have guard : ((HexPolyMathlib.toPolynomial fraction.den).map embedding).eval t ≠ 0 := by
    intro zero
    rw [zero, sign_zero] at denominator
    exact lowest (sign_eq_zero_iff.mp denominator.symm)
  refine ⟨guard, ?_⟩
  by_cases zero : fraction.num = 0
  · simp [evalMapped, zero, HexPolyMathlib.toPolynomial_zero, Hex.OrderedFn.Infinitesimal.sign]
  · rw [Hex.OrderedFn.Infinitesimal.sign, ite_eq_right zero,
      Hex.OrderedFn.Infinitesimal.orderSign_eq, Hex.OrderedFn.Infinitesimal.orderSign_eq,
      Hex.OrderedFn.Infinitesimal.lowestCoeff_eq, Hex.OrderedFn.Infinitesimal.lowestCoeff_eq]
    have inverse (x : ℝ) : SignType.sign x⁻¹ = SignType.sign x := by
      simp only [sign_apply, inv_pos, inv_lt_zero]
    simp only [evalMapped, div_eq_mul_inv, sign_mul, inverse, numerator,
      denominator, SignType.coe_mul]

/-- One neighborhood preserves every sign and denominator guard in finite native
fraction data over the same ordered embedded coefficient field. -/
theorem finite_fractions_map (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (fractions : Finset (Hex.RationalFn F)) :
    ∃ η > (0 : ℝ), ∀ t, 0 < t → t < η → ∀ fraction ∈ fractions,
      ((HexPolyMathlib.toPolynomial fraction.den).map embedding).eval t ≠ 0 ∧
      (SignType.sign (evalMapped embedding fraction t) : Int) =
        Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign fraction := by
  have stable := (eventually_all_finset fractions).mpr
    fun fraction _ => fraction_sign_map embedding ordered fraction
  obtain ⟨η, positive, holds⟩ := Metric.mem_nhdsWithin_iff.mp stable
  refine ⟨η, positive, fun t ht hη => holds ?_⟩
  exact ⟨by simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ht] using hη, ht⟩

/-- One ordinary real parameter below a positive cap realizes the whole finite
collection over a prescribed ordered coefficient embedding. -/
theorem exists_mapped_parameter (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (fractions : Finset (Hex.RationalFn F)) (cap : ℝ) (positive : 0 < cap) :
    ∃ t : ℝ, 0 < t ∧ t < cap ∧ ∀ fraction ∈ fractions,
      ((HexPolyMathlib.toPolynomial fraction.den).map embedding).eval t ≠ 0 ∧
      (SignType.sign (evalMapped embedding fraction t) : Int) =
        Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign fraction := by
  have stable := (eventually_all_finset fractions).mpr
    fun fraction _ => fraction_sign_map embedding ordered fraction
  obtain ⟨t, signs, small⟩ := (stable.and (Ioo_mem_nhdsGT positive)).exists
  exact ⟨t, small.1, small.2, signs⟩

end EmbeddedFractions

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

/-- info: 'Hex.RealClosure.Specialize.polynomial_sign_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.polynomial_sign_map

/-- info: 'Hex.RealClosure.Specialize.fraction_sign_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.fraction_sign_map

/-- info: 'Hex.RealClosure.Specialize.finite_fractions_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.finite_fractions_map

/-- info: 'Hex.RealClosure.Specialize.exists_mapped_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.exists_mapped_parameter

/-- info: 'Hex.RealClosure.Specialize.evalMapped_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.evalMapped_add

/-- info: 'Hex.RealClosure.Specialize.evalMapped_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.evalMapped_mul
