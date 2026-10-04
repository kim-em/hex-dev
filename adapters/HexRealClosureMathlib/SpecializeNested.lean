/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.Specialize

public section

namespace Hex.RealClosure.Specialize

open Polynomial

variable {F : Type} [Field F]

/-- Substitute a coefficient function preserving zero. This operation does
not require the function to preserve arithmetic outside these coefficients. -/
noncomputable def mapCoefficients (f : F → ℝ) (zero : f 0 = 0)
    (p : Polynomial F) : Polynomial ℝ :=
  Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff (p.toFinsupp.coeff.mapRange f zero))

/-- Each coefficient is the actual substituted source coefficient. -/
theorem mapCoefficients_coeff (f : F → ℝ) (zero : f 0 = 0)
    (p : Polynomial F) (i : Nat) :
    (mapCoefficients f zero p).coeff i = f (p.coeff i) := by
  simp [mapCoefficients, Polynomial.coeff]

/-- Reflecting zero on this polynomial's coefficients preserves its least
nonzero exponent and its corresponding coefficient. -/
theorem mapCoefficients_trailing (f : F → ℝ) (zero : f 0 = 0)
    (p : Polynomial F) (reflect : ∀ i, f (p.coeff i) = 0 ↔ p.coeff i = 0) :
    (mapCoefficients f zero p).trailingCoeff = f p.trailingCoeff := by
  have support : (mapCoefficients f zero p).support = p.support := by
    ext i
    simp only [Polynomial.mem_support_iff, mapCoefficients_coeff]
    exact (reflect i).not
  have degree : (mapCoefficients f zero p).natTrailingDegree = p.natTrailingDegree := by
    simp only [Polynomial.natTrailingDegree, Polynomial.trailingDegree, support]
  simp only [Polynomial.trailingCoeff, degree, mapCoefficients_coeff]

section Successive

attribute [local instance 2000] Field.toGrindField
open scoped Hex.OrderedFn.Infinitesimal

/-- A single ordinary parameter preserves every stored coefficient sign and
its actual denominator guard in a finite polynomial family over one
infinitesimal level. The finite family includes zero coefficients too. -/
theorem exists_coefficients_parameter
    (polynomials : Finset (Polynomial (Hex.RationalFn ℝ)))
    (cap : ℝ) (positive : 0 < cap) :
    ∃ t : ℝ, 0 < t ∧ t < cap ∧ ∀ p ∈ polynomials, ∀ i : Nat,
      (HexPolyMathlib.toPolynomial (p.coeff i).den).eval t ≠ 0 ∧
      (SignType.sign (evalFraction (p.coeff i) t) : Int) =
        Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign (p.coeff i) := by
  classical
  let fractions := insert (0 : Hex.RationalFn ℝ)
    (polynomials.biUnion fun p => p.support.image p.coeff)
  obtain ⟨t, ht, below, signs⟩ := exists_fraction_parameter fractions cap positive
  refine ⟨t, ht, below, fun p hp i => signs (p.coeff i) ?_⟩
  by_cases coefficient : p.coeff i = 0
  · simp only [coefficient, fractions, Finset.mem_insert, true_or]
  · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
      ⟨p, hp, Finset.mem_image.mpr ⟨i, Polynomial.mem_support_iff.mpr coefficient, rfl⟩⟩)

/-- Evaluating the stored zero fraction gives zero at every parameter. -/
theorem evalFraction_zero (t : ℝ) : evalFraction (0 : Hex.RationalFn ℝ) t = 0 := by
  simpa only [evalMapped, Polynomial.map_id, evalFraction] using
    evalMapped_zero (RingHom.id ℝ) t

private theorem cast_sign_zero (a : ℝ) : (SignType.sign a : Int) = 0 ↔ a = 0 := by
  rcases lt_trichotomy a 0 with negative | rfl | positive
  · simp [negative, negative.ne]
  · simp
  · simp [positive, positive.ne']

/-- Substitute the first ordinary parameter into the actual coefficients,
then evaluate the resulting polynomial at the second parameter. -/
noncomputable def evalNestedPolynomial (p : Polynomial (Hex.RationalFn ℝ))
    (first second : ℝ) : ℝ :=
  (mapCoefficients (fun q => evalFraction q first) (evalFraction_zero first) p).eval second

/-- The two parameters are chosen together from the actual finite coefficient
family. The second lies below the first, and every polynomial has its native
successive-infinitesimal sign. No sign-agreement hypothesis is supplied. -/
theorem exists_nested_parameters (polynomials : Finset (Polynomial (Hex.RationalFn ℝ)))
    (cap : ℝ) (positive : 0 < cap) :
    ∃ first : ℝ, 0 < first ∧ first < cap ∧
      ∃ second : ℝ, 0 < second ∧ second < first ∧ ∀ p ∈ polynomials,
        (SignType.sign (evalNestedPolynomial p first second) : Int) =
          Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign p.trailingCoeff := by
  classical
  obtain ⟨first, hfirst, below, coefficients⟩ :=
    exists_coefficients_parameter polynomials cap positive
  let f := fun q => evalFraction q first
  let zero := evalFraction_zero first
  let mapped := polynomials.image (mapCoefficients f zero)
  obtain ⟨second, hsecond, ordered, signs⟩ := exists_parameter mapped first hfirst
  refine ⟨first, hfirst, below, second, hsecond, ordered, fun p hp => ?_⟩
  have reflect (i : Nat) : f (p.coeff i) = 0 ↔ p.coeff i = 0 := by
    rw [← cast_sign_zero, (coefficients p hp i).2,
      Hex.OrderedFn.Infinitesimal.sign_eq_zero_iff]
  have stable := signs (mapCoefficients f zero p)
    (Finset.mem_image.mpr ⟨p, hp, rfl⟩)
  have integer := congrArg (fun s : SignType => (s : Int)) stable
  rw [mapCoefficients_trailing f zero p reflect] at integer
  exact integer.trans (coefficients p hp p.natTrailingDegree).2

/-- Evaluate the actual numerator and denominator of a successive-level
canonical fraction using the same two ordinary parameters. -/
noncomputable def evalNestedFraction (fraction : Hex.RationalFn (Hex.RationalFn ℝ))
    (first second : ℝ) : ℝ :=
  evalNestedPolynomial (HexPolyMathlib.toPolynomial fraction.num) first second /
    evalNestedPolynomial (HexPolyMathlib.toPolynomial fraction.den) first second

private theorem evalNestedPolynomial_zero (first second : ℝ) :
    evalNestedPolynomial 0 first second = 0 := by
  have mapped : mapCoefficients (fun q => evalFraction q first)
      (evalFraction_zero first) (0 : Polynomial (Hex.RationalFn ℝ)) = 0 := by
    ext i
    simp only [mapCoefficients_coeff, Polynomial.coeff_zero, evalFraction_zero]
  simp only [evalNestedPolynomial, mapped, Polynomial.eval_zero]

/-- All canonical fractions in the finite family share one ordinary pair.
Every actual denominator remains nonzero and every native successive-level
sign is preserved, including the zero numerator case. -/
theorem exists_nested_fraction_parameters
    (fractions : Finset (Hex.RationalFn (Hex.RationalFn ℝ)))
    (cap : ℝ) (positive : 0 < cap) :
    ∃ first : ℝ, 0 < first ∧ first < cap ∧
      ∃ second : ℝ, 0 < second ∧ second < first ∧ ∀ fraction ∈ fractions,
        evalNestedPolynomial (HexPolyMathlib.toPolynomial fraction.den) first second ≠ 0 ∧
        (SignType.sign (evalNestedFraction fraction first second) : Int) =
          Hex.OrderedFn.Infinitesimal.sign
            (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) fraction := by
  classical
  let polynomials := (fractions.image fun q => HexPolyMathlib.toPolynomial q.num) ∪
    (fractions.image fun q => HexPolyMathlib.toPolynomial q.den)
  obtain ⟨first, hfirst, below, second, hsecond, ordered, signs⟩ :=
    exists_nested_parameters polynomials cap positive
  refine ⟨first, hfirst, below, second, hsecond, ordered, fun fraction present => ?_⟩
  have numerator := signs (HexPolyMathlib.toPolynomial fraction.num)
    (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨fraction, present, rfl⟩))
  have denominator := signs (HexPolyMathlib.toPolynomial fraction.den)
    (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨fraction, present, rfl⟩))
  rw [← Hex.OrderedFn.Infinitesimal.lowestCoeff_eq] at numerator denominator
  have nonzero : HexPolyMathlib.toPolynomial fraction.den ≠ 0 := by
    intro zero
    apply fraction.den_ne_zero
    apply Hex.DensePoly.ext_coeff
    intro i
    have equal := congrArg (fun p : Polynomial (Hex.RationalFn ℝ) => p.coeff i) zero
    simpa only [HexPolyMathlib.coeff_toPolynomial, Polynomial.coeff_zero,
      Hex.DensePoly.coeff_zero] using equal
  have lowest : Hex.OrderedFn.Infinitesimal.lowestCoeff fraction.den ≠ 0 := by
    rw [Hex.OrderedFn.Infinitesimal.lowestCoeff_eq]
    exact trailingCoeff_nonzero_iff_nonzero.mpr nonzero
  have guard : evalNestedPolynomial (HexPolyMathlib.toPolynomial fraction.den) first second ≠ 0 := by
    intro zero
    have vanishes : Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign
        (Hex.OrderedFn.Infinitesimal.lowestCoeff fraction.den) = 0 := by
      simpa only [zero, sign_zero, SignType.coe_zero] using denominator.symm
    exact lowest ((Hex.OrderedFn.Infinitesimal.sign_eq_zero_iff _).mp vanishes)
  refine ⟨guard, ?_⟩
  by_cases zero : fraction.num = 0
  · rw [Hex.OrderedFn.Infinitesimal.sign, ite_eq_left zero]
    simp only [evalNestedFraction, zero, HexPolyMathlib.toPolynomial_zero,
      evalNestedPolynomial_zero, zero_div, sign_zero, SignType.coe_zero]
  · have inverse (a : ℝ) : SignType.sign a⁻¹ = SignType.sign a := by
      simp only [sign_apply, inv_pos, inv_lt_zero]
    rw [Hex.OrderedFn.Infinitesimal.sign, ite_eq_right zero]
    simp only [evalNestedFraction, div_eq_mul_inv, sign_mul, inverse,
      SignType.coe_mul, numerator, denominator]

end Successive

/-- info: 'Hex.RealClosure.Specialize.mapCoefficients_trailing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mapCoefficients_trailing

/-- info: 'Hex.RealClosure.Specialize.exists_nested_parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_nested_parameters

/-- info: 'Hex.RealClosure.Specialize.exists_nested_fraction_parameters' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_nested_fraction_parameters

end Hex.RealClosure.Specialize
