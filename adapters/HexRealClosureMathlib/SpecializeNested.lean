/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.Specialize
public import HexRealClosureMathlib.SpecializeRegular

public section

namespace Hex.RealClosure.Specialize

open Polynomial Filter Topology

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

/-- Every stored coefficient has a nonzero evaluation denominator and its
native infinitesimal sign at this first ordinary parameter. -/
def CoefficientData (p : Polynomial (Hex.RationalFn ℝ)) (t : ℝ) : Prop :=
  ∀ i : Nat, (HexPolyMathlib.toPolynomial (p.coeff i).den).eval t ≠ 0 ∧
    (SignType.sign (evalFraction (p.coeff i) t) : Int) =
      Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign (p.coeff i)

/-- The first-level data holds on one neighborhood, allowing it to be
intersected with other finite replay and root-count requirements. -/
theorem coefficients_near (polynomials : Finset (Polynomial (Hex.RationalFn ℝ))) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ p ∈ polynomials, CoefficientData p t := by
  classical
  let fractions := insert (0 : Hex.RationalFn ℝ)
    (polynomials.biUnion fun p => p.support.image p.coeff)
  have stable : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ q ∈ fractions,
      (HexPolyMathlib.toPolynomial q.den).eval t ≠ 0 ∧
      (SignType.sign (evalFraction q t) : Int) =
        Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign q :=
    (eventually_all_finset fractions).mpr fun q _ => fraction_sign q
  filter_upwards [stable] with t signs
  intro p hp i
  apply signs (p.coeff i)
  by_cases coefficient : p.coeff i = 0
  · simp only [coefficient, fractions, Finset.mem_insert, true_or]
  · exact Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr
      ⟨p, hp, Finset.mem_image.mpr ⟨i, Polynomial.mem_support_iff.mpr coefficient, rfl⟩⟩)

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

/-- First-level data reflects zero on each actual stored coefficient. -/
theorem CoefficientData.zero_iff {p : Polynomial (Hex.RationalFn ℝ)} {t : ℝ}
    (data : CoefficientData p t) (i : Nat) :
    evalFraction (p.coeff i) t = 0 ↔ p.coeff i = 0 := by
  rw [← cast_sign_zero, (data i).2, Hex.OrderedFn.Infinitesimal.sign_eq_zero_iff]

private theorem inner_sign (q : Hex.RationalFn ℝ) :
    Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign q = Hex.OrderedFn.orderSign q := by
  rw [Hex.OrderedFn.Infinitesimal.orderSign_eq]
  rcases lt_trichotomy q 0 with negative | rfl | positive
  · rw [Hex.OrderedFn.Infinitesimal.sign_of_neg negative]
    simp [negative]
  · simp
  · rw [Hex.OrderedFn.Infinitesimal.sign_of_pos positive]
    simp [positive, positive.not_gt]

/-- The actual successive-level native sign reflects canonical zero. -/
theorem nested_sign_zero_iff (fraction : Hex.RationalFn (Hex.RationalFn ℝ)) :
    Hex.OrderedFn.Infinitesimal.sign
      (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) fraction = 0 ↔ fraction = 0 := by
  have signs : (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign : Hex.RationalFn ℝ → Int) =
      Hex.OrderedFn.orderSign := funext inner_sign
  rw [signs]
  exact Hex.OrderedFn.Infinitesimal.sign_eq_zero_iff fraction

/-- Substitute the first ordinary parameter into the actual coefficients,
then evaluate the resulting polynomial at the second parameter. -/
noncomputable def evalNestedPolynomial (p : Polynomial (Hex.RationalFn ℝ))
    (first second : ℝ) : ℝ :=
  (mapCoefficients (fun q => evalFraction q first) (evalFraction_zero first) p).eval second

/-- On nested positive neighborhoods the first-level coefficient data and
second-level polynomial signs hold together. Both neighborhoods can be
intersected with additional replay or selected-root conditions. -/
theorem nested_polynomials_near (polynomials : Finset (Polynomial (Hex.RationalFn ℝ))) :
    ∀ᶠ first in 𝓝[>] (0 : ℝ),
      (∀ p ∈ polynomials, CoefficientData p first) ∧
      ∀ᶠ second in 𝓝[>] (0 : ℝ), ∀ p ∈ polynomials,
        (SignType.sign (evalNestedPolynomial p first second) : Int) =
          Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign p.trailingCoeff := by
  classical
  filter_upwards [coefficients_near polynomials] with first coefficients
  refine ⟨coefficients, ?_⟩
  let f := fun q => evalFraction q first
  let zero := evalFraction_zero first
  have stable : ∀ᶠ second in 𝓝[>] (0 : ℝ), ∀ p ∈ polynomials,
      SignType.sign ((mapCoefficients f zero p).eval second) =
        SignType.sign (mapCoefficients f zero p).trailingCoeff :=
    (eventually_all_finset polynomials).mpr fun p _ => polynomial_sign _
  filter_upwards [stable] with second signs
  intro p hp
  have reflect (i : Nat) : f (p.coeff i) = 0 ↔ p.coeff i = 0 := by
    rw [← cast_sign_zero, (coefficients p hp i).2,
      Hex.OrderedFn.Infinitesimal.sign_eq_zero_iff]
  have integer := congrArg (fun s : SignType => (s : Int)) (signs p hp)
  rw [mapCoefficients_trailing f zero p reflect] at integer
  exact integer.trans (coefficients p hp p.natTrailingDegree).2

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

/-- Nested evaluation uses the existing guarded first-level polynomial
substitution on the actual native coefficient array. -/
theorem nested_polynomial_eq (p : Hex.DensePoly (Hex.RationalFn ℝ)) (first second : ℝ) :
    evalNestedPolynomial (HexPolyMathlib.toPolynomial p) first second =
      (HexPolyMathlib.toPolynomial (polynomial (RingHom.id ℝ) p first)).eval second := by
  unfold evalNestedPolynomial
  apply congrArg (fun p : Polynomial ℝ => p.eval second)
  ext i
  simp only [mapCoefficients_coeff, HexPolyMathlib.coeff_toPolynomial, polynomial_coeff,
    evalFraction, evalMapped, Polynomial.map_id]

private theorem coefficient_regular {p : Hex.DensePoly (Hex.RationalFn ℝ)} {first : ℝ}
    (data : CoefficientData (HexPolyMathlib.toPolynomial p) first) (i : Nat) :
    Regular (RingHom.id ℝ) first (p.coeff i) := by
  simpa only [Regular, Polynomial.map_id, HexPolyMathlib.coeff_toPolynomial] using (data i).1

/-- Actual native addition specializes using the first-level guards; closure
of the existing regular coefficient ring handles intermediate sums. -/
theorem nested_polynomial_add (p q : Hex.DensePoly (Hex.RationalFn ℝ)) (first second : ℝ)
    (left : CoefficientData (HexPolyMathlib.toPolynomial p) first)
    (right : CoefficientData (HexPolyMathlib.toPolynomial q) first) :
    evalNestedPolynomial (HexPolyMathlib.toPolynomial (p + q)) first second =
      evalNestedPolynomial (HexPolyMathlib.toPolynomial p) first second +
        evalNestedPolynomial (HexPolyMathlib.toPolynomial q) first second := by
  rw [nested_polynomial_eq, polynomial_add (RingHom.id ℝ) first p q
    (fun i _ => coefficient_regular left i) (fun i _ => coefficient_regular right i),
    HexPolyMathlib.toPolynomial_add, Polynomial.eval_add,
    ← nested_polynomial_eq, ← nested_polynomial_eq]

/-- Actual native multiplication specializes through the same guarded
coefficient ring, without a homomorphism on the whole infinitesimal field. -/
theorem nested_polynomial_mul (p q : Hex.DensePoly (Hex.RationalFn ℝ)) (first second : ℝ)
    (left : CoefficientData (HexPolyMathlib.toPolynomial p) first)
    (right : CoefficientData (HexPolyMathlib.toPolynomial q) first) :
    evalNestedPolynomial (HexPolyMathlib.toPolynomial (p * q)) first second =
      evalNestedPolynomial (HexPolyMathlib.toPolynomial p) first second *
        evalNestedPolynomial (HexPolyMathlib.toPolynomial q) first second := by
  rw [nested_polynomial_eq, polynomial_mul (RingHom.id ℝ) first p q
    (fun i _ => coefficient_regular left i) (fun i _ => coefficient_regular right i),
    HexPolyMathlib.toPolynomial_mul, Polynomial.eval_mul,
    ← nested_polynomial_eq, ← nested_polynomial_eq]

private theorem nested_lift_eval (p : Hex.DensePoly (Hex.RationalFn ℝ))
    (first second : ℝ) (P : Polynomial (regularRing (RingHom.id ℝ) first))
    (lift : P.map (regularRing (RingHom.id ℝ) first).subtype = HexPolyMathlib.toPolynomial p) :
    evalNestedPolynomial (HexPolyMathlib.toPolynomial p) first second =
      (P.map (evaluation (RingHom.id ℝ) first)).eval second := by
  rw [nested_polynomial_eq, polynomial_map (RingHom.id ℝ) first p P lift]

/-- Canonical outer fraction addition specializes at the same ordinary pair.
Only the actual stored coefficient guards and three outer denominator guards
are used; no interpretation of the whole infinitesimal field is assumed. -/
theorem nested_fraction_add (f g : Hex.RationalFn (Hex.RationalFn ℝ)) (first second : ℝ)
    (left : CoefficientData (HexPolyMathlib.toPolynomial f.num) first ∧
      CoefficientData (HexPolyMathlib.toPolynomial f.den) first)
    (right : CoefficientData (HexPolyMathlib.toPolynomial g.num) first ∧
      CoefficientData (HexPolyMathlib.toPolynomial g.den) first)
    (sum : CoefficientData (HexPolyMathlib.toPolynomial (f + g).num) first ∧
      CoefficientData (HexPolyMathlib.toPolynomial (f + g).den) first)
    (leftDen : evalNestedPolynomial (HexPolyMathlib.toPolynomial f.den) first second ≠ 0)
    (rightDen : evalNestedPolynomial (HexPolyMathlib.toPolynomial g.den) first second ≠ 0)
    (sumDen : evalNestedPolynomial (HexPolyMathlib.toPolynomial (f + g).den) first second ≠ 0) :
    evalNestedFraction (f + g) first second =
      evalNestedFraction f first second + evalNestedFraction g first second := by
  classical
  obtain ⟨FN, hfn⟩ := polynomial_lift (RingHom.id ℝ) first f.num
    (fun i _ => coefficient_regular left.1 i)
  obtain ⟨FD, hfd⟩ := polynomial_lift (RingHom.id ℝ) first f.den
    (fun i _ => coefficient_regular left.2 i)
  obtain ⟨GN, hgn⟩ := polynomial_lift (RingHom.id ℝ) first g.num
    (fun i _ => coefficient_regular right.1 i)
  obtain ⟨GD, hgd⟩ := polynomial_lift (RingHom.id ℝ) first g.den
    (fun i _ => coefficient_regular right.2 i)
  obtain ⟨SN, hsn⟩ := polynomial_lift (RingHom.id ℝ) first (f + g).num
    (fun i _ => coefficient_regular sum.1 i)
  obtain ⟨SD, hsd⟩ := polynomial_lift (RingHom.id ℝ) first (f + g).den
    (fun i _ => coefficient_regular sum.2 i)
  have cross : SN * (FD * GD) = (FN * GD + GN * FD) * SD := by
    apply Polynomial.map_injective (regularRing (RingHom.id ℝ) first).subtype
      (regularRing (RingHom.id ℝ) first).subtype_injective
    simp only [Polynomial.map_mul, Polynomial.map_add, hfn, hfd, hgn, hgd, hsn, hsd]
    simpa only [HexPolyMathlib.toPolynomial_mul, HexPolyMathlib.toPolynomial_add] using
      congrArg HexPolyMathlib.toPolynomial (Hex.RationalFn.add_spec f g)
  have specialized := congrArg
    (fun p => (p.map (evaluation (RingHom.id ℝ) first)).eval second) cross
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.eval_mul,
    Polynomial.eval_add, ← nested_lift_eval f.num first second FN hfn,
    ← nested_lift_eval f.den first second FD hfd, ← nested_lift_eval g.num first second GN hgn,
    ← nested_lift_eval g.den first second GD hgd, ← nested_lift_eval (f + g).num first second SN hsn,
    ← nested_lift_eval (f + g).den first second SD hsd] at specialized
  unfold evalNestedFraction
  rw [div_add_div _ _ leftDen rightDen]
  apply (div_eq_div_iff sumDen (mul_ne_zero leftDen rightDen)).mpr
  simpa only [mul_comm] using specialized

/-- Canonical outer fraction multiplication specializes at the same ordinary pair.
Only the actual stored coefficient guards and three outer denominator guards
are used; no interpretation of the whole infinitesimal field is assumed. -/
theorem nested_fraction_mul (f g : Hex.RationalFn (Hex.RationalFn ℝ)) (first second : ℝ)
    (left : CoefficientData (HexPolyMathlib.toPolynomial f.num) first ∧
      CoefficientData (HexPolyMathlib.toPolynomial f.den) first)
    (right : CoefficientData (HexPolyMathlib.toPolynomial g.num) first ∧
      CoefficientData (HexPolyMathlib.toPolynomial g.den) first)
    (product : CoefficientData (HexPolyMathlib.toPolynomial (f * g).num) first ∧
      CoefficientData (HexPolyMathlib.toPolynomial (f * g).den) first)
    (leftDen : evalNestedPolynomial (HexPolyMathlib.toPolynomial f.den) first second ≠ 0)
    (rightDen : evalNestedPolynomial (HexPolyMathlib.toPolynomial g.den) first second ≠ 0)
    (productDen : evalNestedPolynomial (HexPolyMathlib.toPolynomial (f * g).den) first second ≠ 0) :
    evalNestedFraction (f * g) first second =
      evalNestedFraction f first second * evalNestedFraction g first second := by
  classical
  obtain ⟨FN, hfn⟩ := polynomial_lift (RingHom.id ℝ) first f.num
    (fun i _ => coefficient_regular left.1 i)
  obtain ⟨FD, hfd⟩ := polynomial_lift (RingHom.id ℝ) first f.den
    (fun i _ => coefficient_regular left.2 i)
  obtain ⟨GN, hgn⟩ := polynomial_lift (RingHom.id ℝ) first g.num
    (fun i _ => coefficient_regular right.1 i)
  obtain ⟨GD, hgd⟩ := polynomial_lift (RingHom.id ℝ) first g.den
    (fun i _ => coefficient_regular right.2 i)
  obtain ⟨SN, hsn⟩ := polynomial_lift (RingHom.id ℝ) first (f * g).num
    (fun i _ => coefficient_regular product.1 i)
  obtain ⟨SD, hsd⟩ := polynomial_lift (RingHom.id ℝ) first (f * g).den
    (fun i _ => coefficient_regular product.2 i)
  have cross : SN * (FD * GD) = (FN * GN) * SD := by
    apply Polynomial.map_injective (regularRing (RingHom.id ℝ) first).subtype
      (regularRing (RingHom.id ℝ) first).subtype_injective
    simp only [Polynomial.map_mul, Polynomial.map_add, hfn, hfd, hgn, hgd, hsn, hsd]
    simpa only [HexPolyMathlib.toPolynomial_mul, HexPolyMathlib.toPolynomial_add] using
      congrArg HexPolyMathlib.toPolynomial (Hex.RationalFn.mul_spec f g)
  have specialized := congrArg
    (fun p => (p.map (evaluation (RingHom.id ℝ) first)).eval second) cross
  simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.eval_mul,
    Polynomial.eval_add, ← nested_lift_eval f.num first second FN hfn,
    ← nested_lift_eval f.den first second FD hfd, ← nested_lift_eval g.num first second GN hgn,
    ← nested_lift_eval g.den first second GD hgd, ← nested_lift_eval (f * g).num first second SN hsn,
    ← nested_lift_eval (f * g).den first second SD hsd] at specialized
  unfold evalNestedFraction
  rw [div_mul_div_comm]
  apply (div_eq_div_iff productDen (mul_ne_zero leftDen rightDen)).mpr
  simpa only [mul_comm] using specialized

/-- Total canonical inversion preserves ordinary evaluation at the same pair
when the actual finite data reflects zero and the stored guards hold. -/
theorem nested_fraction_inv (f : Hex.RationalFn (Hex.RationalFn ℝ)) (first second : ℝ)
    (input : CoefficientData (HexPolyMathlib.toPolynomial f.num) first ∧
      CoefficientData (HexPolyMathlib.toPolynomial f.den) first)
    (inverse : CoefficientData (HexPolyMathlib.toPolynomial f⁻¹.num) first ∧
      CoefficientData (HexPolyMathlib.toPolynomial f⁻¹.den) first)
    (inverseDen : evalNestedPolynomial (HexPolyMathlib.toPolynomial f⁻¹.den) first second ≠ 0)
    (reflects : evalNestedFraction f first second = 0 ↔ f = 0) :
    evalNestedFraction f⁻¹ first second = (evalNestedFraction f first second)⁻¹ := by
  classical
  by_cases zero : f = 0
  · subst f
    have value : evalNestedFraction (0 : Hex.RationalFn (Hex.RationalFn ℝ)) first second = 0 := by
      change evalNestedPolynomial (HexPolyMathlib.toPolynomial (0 : Hex.DensePoly (Hex.RationalFn ℝ)))
        first second / _ = 0
      rw [HexPolyMathlib.toPolynomial_zero, evalNestedPolynomial_zero, zero_div]
    rw [inv_zero, value, inv_zero]
  · have numerator : evalNestedPolynomial (HexPolyMathlib.toPolynomial f.num) first second ≠ 0 := by
      intro vanishes
      apply zero
      apply reflects.mp
      unfold evalNestedFraction
      rw [vanishes, zero_div]
    obtain ⟨FN, hfn⟩ := polynomial_lift (RingHom.id ℝ) first f.num
      (fun i _ => coefficient_regular input.1 i)
    obtain ⟨FD, hfd⟩ := polynomial_lift (RingHom.id ℝ) first f.den
      (fun i _ => coefficient_regular input.2 i)
    obtain ⟨IN, hin⟩ := polynomial_lift (RingHom.id ℝ) first f⁻¹.num
      (fun i _ => coefficient_regular inverse.1 i)
    obtain ⟨ID, hid⟩ := polynomial_lift (RingHom.id ℝ) first f⁻¹.den
      (fun i _ => coefficient_regular inverse.2 i)
    have cross : IN * FN = FD * ID := by
      apply Polynomial.map_injective (regularRing (RingHom.id ℝ) first).subtype
        (regularRing (RingHom.id ℝ) first).subtype_injective
      simp only [Polynomial.map_mul, hfn, hfd, hin, hid]
      simpa only [HexPolyMathlib.toPolynomial_mul] using congrArg HexPolyMathlib.toPolynomial
        (Hex.RationalFn.inv_spec f ((Hex.RationalFn.num_eq_zero f).not.mpr zero))
    have specialized := congrArg
      (fun p => (p.map (evaluation (RingHom.id ℝ) first)).eval second) cross
    simp only [Polynomial.map_mul, Polynomial.eval_mul,
      ← nested_lift_eval f.num first second FN hfn, ← nested_lift_eval f.den first second FD hfd,
      ← nested_lift_eval f⁻¹.num first second IN hin, ← nested_lift_eval f⁻¹.den first second ID hid]
      at specialized
    unfold evalNestedFraction
    rw [inv_div]
    exact (div_eq_div_iff inverseDen numerator).mpr specialized

private theorem nested_fraction_sign
    (fraction : Hex.RationalFn (Hex.RationalFn ℝ)) (first second : ℝ)
    (numerator : (SignType.sign (evalNestedPolynomial
      (HexPolyMathlib.toPolynomial fraction.num) first second) : Int) =
        Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign
          (HexPolyMathlib.toPolynomial fraction.num).trailingCoeff)
    (denominator : (SignType.sign (evalNestedPolynomial
      (HexPolyMathlib.toPolynomial fraction.den) first second) : Int) =
        Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign
          (HexPolyMathlib.toPolynomial fraction.den).trailingCoeff) :
    evalNestedPolynomial (HexPolyMathlib.toPolynomial fraction.den) first second ≠ 0 ∧
      (SignType.sign (evalNestedFraction fraction first second) : Int) =
        Hex.OrderedFn.Infinitesimal.sign
          (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) fraction := by
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
  exact nested_fraction_sign fraction first second numerator denominator

/-- The actual numerator and denominator coefficient guards are retained on
the first neighborhood. On the second neighborhood all outer denominator
guards and signs hold together, so further finite requirements can compose. -/
theorem nested_fractions_near (fractions : Finset (Hex.RationalFn (Hex.RationalFn ℝ))) :
    ∀ᶠ first in 𝓝[>] (0 : ℝ),
      (∀ fraction ∈ fractions,
        CoefficientData (HexPolyMathlib.toPolynomial fraction.num) first ∧
        CoefficientData (HexPolyMathlib.toPolynomial fraction.den) first) ∧
      ∀ᶠ second in 𝓝[>] (0 : ℝ), ∀ fraction ∈ fractions,
        evalNestedPolynomial (HexPolyMathlib.toPolynomial fraction.den) first second ≠ 0 ∧
        (SignType.sign (evalNestedFraction fraction first second) : Int) =
          Hex.OrderedFn.Infinitesimal.sign
            (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) fraction ∧
        (evalNestedFraction fraction first second = 0 ↔ fraction = 0) := by
  classical
  let polynomials := (fractions.image fun q => HexPolyMathlib.toPolynomial q.num) ∪
    (fractions.image fun q => HexPolyMathlib.toPolynomial q.den)
  filter_upwards [nested_polynomials_near polynomials] with first data
  refine ⟨fun fraction present => ⟨?_, ?_⟩, ?_⟩
  · exact data.1 _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨fraction, present, rfl⟩))
  · exact data.1 _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨fraction, present, rfl⟩))
  · filter_upwards [data.2] with second signs
    intro fraction present
    obtain ⟨guard, agreement⟩ := nested_fraction_sign fraction first second
      (signs _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨fraction, present, rfl⟩)))
      (signs _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨fraction, present, rfl⟩)))
    refine ⟨guard, agreement, ?_⟩
    rw [← cast_sign_zero, agreement, nested_sign_zero_iff]

/-- At one ordinary parameter pair, every recorded sign and arithmetic step
in a finite family is preserved together. Membership requires recording each
actual result; it does not assume any coefficient interpretation laws. -/
theorem nested_arithmetic_near (fractions : Finset (Hex.RationalFn (Hex.RationalFn ℝ))) :
    ∀ᶠ first in 𝓝[>] (0 : ℝ), ∀ᶠ second in 𝓝[>] (0 : ℝ),
      (∀ f ∈ fractions,
        (SignType.sign (evalNestedFraction f first second) : Int) =
          Hex.OrderedFn.Infinitesimal.sign
            (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) f ∧
        (evalNestedFraction f first second = 0 ↔ f = 0)) ∧
      (∀ f ∈ fractions, ∀ g ∈ fractions, f + g ∈ fractions →
        evalNestedFraction (f + g) first second =
          evalNestedFraction f first second + evalNestedFraction g first second) ∧
      (∀ f ∈ fractions, ∀ g ∈ fractions, f * g ∈ fractions →
        evalNestedFraction (f * g) first second =
          evalNestedFraction f first second * evalNestedFraction g first second) ∧
      (∀ f ∈ fractions, f⁻¹ ∈ fractions →
        evalNestedFraction f⁻¹ first second = (evalNestedFraction f first second)⁻¹) := by
  filter_upwards [nested_fractions_near fractions] with first coefficients
  filter_upwards [coefficients.2] with second values
  refine ⟨fun f hf => (values f hf).2, ?_, ?_, ?_⟩
  · intro f hf g hg hsum
    exact nested_fraction_add f g first second (coefficients.1 f hf) (coefficients.1 g hg)
      (coefficients.1 (f + g) hsum) (values f hf).1 (values g hg).1 (values (f + g) hsum).1
  · intro f hf g hg hproduct
    exact nested_fraction_mul f g first second (coefficients.1 f hf) (coefficients.1 g hg)
      (coefficients.1 (f * g) hproduct) (values f hf).1 (values g hg).1
      (values (f * g) hproduct).1
  · intro f hf hinverse
    exact nested_fraction_inv f first second (coefficients.1 f hf) (coefficients.1 f⁻¹ hinverse)
      (values f⁻¹ hinverse).1 (values f hf).2.2

/-- One positive ordinary pair below the requested cap preserves the entire
recorded finite family, including successive-parameter order and arithmetic. -/
theorem exists_nested_arithmetic (fractions : Finset (Hex.RationalFn (Hex.RationalFn ℝ)))
    (cap : ℝ) (positive : 0 < cap) :
    ∃ first : ℝ, 0 < first ∧ first < cap ∧
      ∃ second : ℝ, 0 < second ∧ second < first ∧
      (∀ f ∈ fractions,
        (SignType.sign (evalNestedFraction f first second) : Int) =
          Hex.OrderedFn.Infinitesimal.sign
            (Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign) f ∧
        (evalNestedFraction f first second = 0 ↔ f = 0)) ∧
      (∀ f ∈ fractions, ∀ g ∈ fractions, f + g ∈ fractions →
        evalNestedFraction (f + g) first second =
          evalNestedFraction f first second + evalNestedFraction g first second) ∧
      (∀ f ∈ fractions, ∀ g ∈ fractions, f * g ∈ fractions →
        evalNestedFraction (f * g) first second =
          evalNestedFraction f first second * evalNestedFraction g first second) ∧
      (∀ f ∈ fractions, f⁻¹ ∈ fractions →
        evalNestedFraction f⁻¹ first second = (evalNestedFraction f first second)⁻¹) := by
  have firstSmall : ∀ᶠ first in 𝓝[>] (0 : ℝ), first < cap :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds positive)
  have firstPositive : ∀ᶠ first in 𝓝[>] (0 : ℝ), 0 < first := self_mem_nhdsWithin
  obtain ⟨first, ⟨data, belowCap⟩, hfirst⟩ :=
    (((nested_arithmetic_near fractions).and firstSmall).and firstPositive).exists
  have secondSmall : ∀ᶠ second in 𝓝[>] (0 : ℝ), second < first :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hfirst)
  have secondPositive : ∀ᶠ second in 𝓝[>] (0 : ℝ), 0 < second := self_mem_nhdsWithin
  obtain ⟨second, ⟨preserved, below⟩, hsecond⟩ := ((data.and secondSmall).and secondPositive).exists
  exact ⟨first, hfirst, belowCap, second, hsecond, below, preserved⟩

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

/-- info: 'Hex.RealClosure.Specialize.coefficients_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.coefficients_near

/-- info: 'Hex.RealClosure.Specialize.nested_polynomials_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.nested_polynomials_near

/-- info: 'Hex.RealClosure.Specialize.nested_fractions_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.nested_fractions_near

/-- info: 'Hex.RealClosure.Specialize.nested_fraction_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.nested_fraction_add

/-- info: 'Hex.RealClosure.Specialize.nested_fraction_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.nested_fraction_mul

/-- info: 'Hex.RealClosure.Specialize.nested_fraction_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.nested_fraction_inv

/-- info: 'Hex.RealClosure.Specialize.nested_arithmetic_near' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.nested_arithmetic_near

/-- info: 'Hex.RealClosure.Specialize.exists_nested_arithmetic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.exists_nested_arithmetic
