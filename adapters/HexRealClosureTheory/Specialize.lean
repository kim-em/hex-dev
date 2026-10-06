/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexOrderedFnTheory.Infinitesimal
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
  (HexPolyTheory.toPolynomial f.num).eval t / (HexPolyTheory.toPolynomial f.den).eval t

/-- Actual native lowest-coefficient signs agree with real evaluation near zero. -/
theorem native_polynomial_sign (p : Hex.DensePoly ℝ) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), SignType.sign ((HexPolyTheory.toPolynomial p).eval t) =
      SignType.sign (Hex.OrderedFn.Infinitesimal.lowestCoeff p) := by
  rw [Hex.OrderedFn.Infinitesimal.lowestCoeff_eq]
  exact polynomial_sign _

/-- Every stored canonical fraction has one neighborhood preserving its actual
infinitesimal sign and the nonzero denominator needed for specialization. -/
theorem fraction_sign (f : Hex.RationalFn ℝ) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (HexPolyTheory.toPolynomial f.den).eval t ≠ 0 ∧
      (SignType.sign (evalFraction f t) : Int) =
        Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign f := by
  have nonzero : HexPolyTheory.toPolynomial f.den ≠ 0 := by
    intro zero
    apply f.den_ne_zero
    apply Hex.DensePoly.ext_coeff
    intro i
    have equal := congrArg (fun p : Polynomial ℝ => p.coeff i) zero
    simpa only [HexPolyTheory.coeff_toPolynomial, Polynomial.coeff_zero,
      Hex.DensePoly.coeff_zero] using equal
  have lowest : Hex.OrderedFn.Infinitesimal.lowestCoeff f.den ≠ 0 := by
    rw [Hex.OrderedFn.Infinitesimal.lowestCoeff_eq]
    exact trailingCoeff_nonzero_iff_nonzero.mpr nonzero
  filter_upwards [native_polynomial_sign f.num, native_polynomial_sign f.den] with t numerator denominator
  have guard : (HexPolyTheory.toPolynomial f.den).eval t ≠ 0 := by
    intro zero
    rw [zero, sign_zero] at denominator
    exact lowest (sign_eq_zero_iff.mp denominator.symm)
  refine ⟨guard, ?_⟩
  by_cases zero : f.num = 0
  · simp [evalFraction, zero, HexPolyTheory.toPolynomial_zero, Hex.OrderedFn.Infinitesimal.sign]
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
      (HexPolyTheory.toPolynomial f.den).eval t ≠ 0 ∧
      (SignType.sign (evalFraction f t) : Int) =
        Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign f := by
  have stable : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ f ∈ fractions,
      (HexPolyTheory.toPolynomial f.den).eval t ≠ 0 ∧
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
      (HexPolyTheory.toPolynomial f.den).eval t ≠ 0 ∧
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
  ((HexPolyTheory.toPolynomial fraction.num).map embedding).eval t /
    ((HexPolyTheory.toPolynomial fraction.den).map embedding).eval t

/-- Stored canonical numerator/denominator evaluation agrees with Mathlib's
rational-function evaluation through the proved native correspondence. -/
theorem evalMapped_eq_eval (embedding : F →+* ℝ) (fraction : Hex.RationalFn F) (t : ℝ) :
    evalMapped embedding fraction t = RatFunc.eval embedding t (HexRationalFnTheory.toRatFunc fraction) := by
  unfold evalMapped RatFunc.eval
  rw [← HexRationalFnTheory.num_toRatFunc, ← HexRationalFnTheory.den_toRatFunc,
    Polynomial.eval_map, Polynomial.eval_map]

/-- Specialization preserves an actual native sum whenever the two operand
denominators are nonzero. Canonical reduction supplies the result guard. -/
theorem evalMapped_add (embedding : F →+* ℝ) (first second : Hex.RationalFn F) (t : ℝ)
    (left : ((HexPolyTheory.toPolynomial first.den).map embedding).eval t ≠ 0)
    (right : ((HexPolyTheory.toPolynomial second.den).map embedding).eval t ≠ 0) :
    evalMapped embedding (first + second) t =
      evalMapped embedding first t + evalMapped embedding second t := by
  simp only [evalMapped_eq_eval, HexRationalFnTheory.toRatFunc_add]
  exact RatFunc.eval_add embedding t
    (by simpa only [← HexRationalFnTheory.den_toRatFunc, Polynomial.eval_map] using left)
    (by simpa only [← HexRationalFnTheory.den_toRatFunc, Polynomial.eval_map] using right)

/-- Specialization preserves an actual native product whenever the two operand
denominators are nonzero. Canonical reduction supplies the result guard. -/
theorem evalMapped_mul (embedding : F →+* ℝ) (first second : Hex.RationalFn F) (t : ℝ)
    (left : ((HexPolyTheory.toPolynomial first.den).map embedding).eval t ≠ 0)
    (right : ((HexPolyTheory.toPolynomial second.den).map embedding).eval t ≠ 0) :
    evalMapped embedding (first * second) t =
      evalMapped embedding first t * evalMapped embedding second t := by
  simp only [evalMapped_eq_eval, HexRationalFnTheory.toRatFunc_mul]
  exact RatFunc.eval_mul embedding t
    (by simpa only [← HexRationalFnTheory.den_toRatFunc, Polynomial.eval_map] using left)
    (by simpa only [← HexRationalFnTheory.den_toRatFunc, Polynomial.eval_map] using right)

/-- An actual polynomial fraction evaluates as its mapped polynomial. -/
theorem evalMapped_ofPoly (embedding : F →+* ℝ) (p : Hex.DensePoly F) (t : ℝ) :
    evalMapped embedding (Hex.RationalFn.ofPoly p) t =
      ((HexPolyTheory.toPolynomial p).map embedding).eval t := by
  change ((HexPolyTheory.toPolynomial p).map embedding).eval t /
    ((HexPolyTheory.toPolynomial (1 : Hex.DensePoly F)).map embedding).eval t = _
  rw [HexPolyTheory.toPolynomial_one, Polynomial.map_one, Polynomial.eval_one, div_one]

/-- Stored coefficient constants specialize through the prescribed embedding. -/
theorem evalMapped_C (embedding : F →+* ℝ) (a : F) (t : ℝ) :
    evalMapped embedding (Hex.RationalFn.C a) t = embedding a := by
  rw [Hex.RationalFn.C, evalMapped_ofPoly, HexPolyTheory.toPolynomial_C,
    Polynomial.map_C, Polynomial.eval_C]

/-- The stored indeterminate specializes to the chosen ordinary parameter. -/
theorem evalMapped_X (embedding : F →+* ℝ) (t : ℝ) :
    evalMapped embedding (Hex.RationalFn.X : Hex.RationalFn F) t = t := by
  rw [Hex.RationalFn.X, evalMapped_ofPoly, HexPolyTheory.toPolynomial_monomial,
    Polynomial.map_monomial, Polynomial.eval_monomial]
  simp

/-- Canonical zero specializes to ordinary real zero. -/
theorem evalMapped_zero (embedding : F →+* ℝ) (t : ℝ) :
    evalMapped embedding (0 : Hex.RationalFn F) t = 0 := by
  rw [← Hex.RationalFn.ofPoly_zero, evalMapped_ofPoly, HexPolyTheory.toPolynomial_zero,
    Polynomial.map_zero, Polynomial.eval_zero]

/-- Canonical one specializes to ordinary real one. -/
theorem evalMapped_one (embedding : F →+* ℝ) (t : ℝ) :
    evalMapped embedding (1 : Hex.RationalFn F) t = 1 := by
  rw [← Hex.RationalFn.ofPoly_one, evalMapped_ofPoly, HexPolyTheory.toPolynomial_one,
    Polynomial.map_one, Polynomial.eval_one]

/-- Native natural casts retain their exact ordinary real value. -/
theorem evalMapped_nat (embedding : F →+* ℝ) (n : Nat) (t : ℝ) :
    evalMapped embedding (n : Hex.RationalFn F) t = (n : ℝ) := by
  change evalMapped embedding (Hex.RationalFn.ofPoly (n : Hex.DensePoly F)) t = _
  have polynomial : HexPolyTheory.toPolynomial (n : Hex.DensePoly F) = (n : Polynomial F) := by
    apply Polynomial.ext
    intro i
    simp only [HexPolyTheory.coeff_toPolynomial, Hex.DensePoly.coeff_natCast, Polynomial.coeff_natCast_ite,
      Nat.cast_ite, Nat.cast_zero]
  rw [evalMapped_ofPoly, polynomial, Polynomial.map_natCast, Polynomial.eval_natCast]

/-- Negation changes only the stored numerator and commutes with specialization. -/
theorem evalMapped_neg (embedding : F →+* ℝ) (fraction : Hex.RationalFn F) (t : ℝ) :
    evalMapped embedding (-fraction) t = -evalMapped embedding fraction t := by
  change ((HexPolyTheory.toPolynomial (-fraction.num)).map embedding).eval t /
    ((HexPolyTheory.toPolynomial fraction.den).map embedding).eval t =
      -(((HexPolyTheory.toPolynomial fraction.num).map embedding).eval t /
        ((HexPolyTheory.toPolynomial fraction.den).map embedding).eval t)
  rw [HexPolyTheory.toPolynomial_neg, Polynomial.map_neg, Polynomial.eval_neg, neg_div]

/-- Native integer casts retain their exact ordinary real value. -/
theorem evalMapped_int (embedding : F →+* ℝ) (n : Int) (t : ℝ) :
    evalMapped embedding (n : Hex.RationalFn F) t = (n : ℝ) := by
  cases n with
  | ofNat n => simpa only [Int.ofNat_eq_natCast, Int.cast_natCast] using evalMapped_nat embedding n t
  | negSucc n => rw [Int.cast_negSucc, evalMapped_neg, evalMapped_nat, Int.cast_negSucc]

/-- Native subtraction specializes under the two operand guards. -/
theorem evalMapped_sub (embedding : F →+* ℝ) (first second : Hex.RationalFn F) (t : ℝ)
    (left : ((HexPolyTheory.toPolynomial first.den).map embedding).eval t ≠ 0)
    (right : ((HexPolyTheory.toPolynomial second.den).map embedding).eval t ≠ 0) :
    evalMapped embedding (first - second) t =
      evalMapped embedding first t - evalMapped embedding second t := by
  have negative : ((HexPolyTheory.toPolynomial (-second).den).map embedding).eval t ≠ 0 := right
  simpa only [sub_eq_add_neg, evalMapped_neg] using
    evalMapped_add embedding first (-second) t left negative

/-- Native inversion swaps the canonical numerator and denominator up to
one nonzero coefficient scale, so evaluation commutes with total inversion
at every parameter, including zeros and poles. -/
theorem evalMapped_inv (embedding : F →+* ℝ) (fraction : Hex.RationalFn F) (t : ℝ) :
    evalMapped embedding fraction⁻¹ t = (evalMapped embedding fraction t)⁻¹ := by
  by_cases hn : fraction.num = 0
  · have hf := (Hex.RationalFn.num_eq_zero fraction).mp hn
    subst fraction
    simp only [inv_zero, evalMapped_zero]
  · change evalMapped embedding (Hex.RationalFn.inv fraction) t = _
    simp only [Hex.RationalFn.inv, hn, ↓reduceDIte]
    split
    · change ((HexPolyTheory.toPolynomial fraction.den).map embedding).eval t /
        ((HexPolyTheory.toPolynomial fraction.num).map embedding).eval t = _
      exact (inv_div _ _).symm
    · have scale : embedding fraction.num.leadingCoeff⁻¹ ≠ 0 :=
        (_root_.map_ne_zero embedding).mpr (inv_ne_zero (Hex.DensePoly.leadingCoeff_ne_zero hn))
      simp only [evalMapped, Hex.RationalFn.ofCoprime, HexPolyTheory.toPolynomial_scale,
        Polynomial.map_mul, Polynomial.map_C, Polynomial.eval_mul, Polynomial.eval_C]
      rw [mul_div_mul_left _ _ scale, inv_div]

/-- Native division specializes when its first operand and the inverse of
its second operand have nonzero denominators. -/
theorem evalMapped_div (embedding : F →+* ℝ) (first second : Hex.RationalFn F) (t : ℝ)
    (left : ((HexPolyTheory.toPolynomial first.den).map embedding).eval t ≠ 0)
    (inverse : ((HexPolyTheory.toPolynomial second⁻¹.den).map embedding).eval t ≠ 0) :
    evalMapped embedding (first / second) t =
      evalMapped embedding first t / evalMapped embedding second t := by
  rw [div_eq_mul_inv, evalMapped_mul embedding first second⁻¹ t left inverse,
    evalMapped_inv embedding second t, div_eq_mul_inv]

private theorem polynomial_pow (p : Hex.DensePoly F) (n : Nat) :
    HexPolyTheory.toPolynomial (p ^ n) = (HexPolyTheory.toPolynomial p) ^ n := by
  induction n with
  | zero => rw [Lean.Grind.Semiring.pow_zero, HexPolyTheory.toPolynomial_one, pow_zero]
  | succ n ih => rw [Lean.Grind.Semiring.pow_succ, HexPolyTheory.toPolynomial_mul, ih, pow_succ]

/-- Canonical native powers raise the stored numerator and denominator
separately. Evaluation therefore commutes with powers even at poles. -/
theorem evalMapped_pow (embedding : F →+* ℝ) (fraction : Hex.RationalFn F) (t : ℝ) (n : Nat) :
    evalMapped embedding (fraction ^ n) t = (evalMapped embedding fraction t) ^ n := by
  simp only [evalMapped, Hex.RationalFn.num_pow, Hex.RationalFn.den_pow,
    polynomial_pow, Polynomial.map_pow, Polynomial.eval_pow, div_pow]

variable [LinearOrder F]

/-- Ordered coefficient embeddings preserve each native fraction's infinitesimal
sign on one positive neighborhood, including its actual denominator guard. -/
theorem fraction_sign_map (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (fraction : Hex.RationalFn F) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ((HexPolyTheory.toPolynomial fraction.den).map embedding).eval t ≠ 0 ∧
      (SignType.sign (evalMapped embedding fraction t) : Int) =
        Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign fraction := by
  have nonzero : HexPolyTheory.toPolynomial fraction.den ≠ 0 := by
    intro zero
    apply fraction.den_ne_zero
    apply Hex.DensePoly.ext_coeff
    intro i
    have equal := congrArg (fun p : Polynomial F => p.coeff i) zero
    simpa only [HexPolyTheory.coeff_toPolynomial, Polynomial.coeff_zero,
      Hex.DensePoly.coeff_zero] using equal
  have lowest : (HexPolyTheory.toPolynomial fraction.den).trailingCoeff ≠ 0 :=
    trailingCoeff_nonzero_iff_nonzero.mpr nonzero
  filter_upwards [polynomial_sign_map embedding ordered (HexPolyTheory.toPolynomial fraction.num),
    polynomial_sign_map embedding ordered (HexPolyTheory.toPolynomial fraction.den)] with t numerator denominator
  have guard : ((HexPolyTheory.toPolynomial fraction.den).map embedding).eval t ≠ 0 := by
    intro zero
    rw [zero, sign_zero] at denominator
    exact lowest (sign_eq_zero_iff.mp denominator.symm)
  refine ⟨guard, ?_⟩
  by_cases zero : fraction.num = 0
  · simp [evalMapped, zero, HexPolyTheory.toPolynomial_zero, Hex.OrderedFn.Infinitesimal.sign]
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
      ((HexPolyTheory.toPolynomial fraction.den).map embedding).eval t ≠ 0 ∧
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
      ((HexPolyTheory.toPolynomial fraction.den).map embedding).eval t ≠ 0 ∧
      (SignType.sign (evalMapped embedding fraction t) : Int) =
        Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign fraction := by
  have stable := (eventually_all_finset fractions).mpr
    fun fraction _ => fraction_sign_map embedding ordered fraction
  obtain ⟨t, signs, small⟩ := (stable.and (Ioo_mem_nhdsGT positive)).exists
  exact ⟨t, small.1, small.2, signs⟩

/-- A caller-supplied predecessor sign can be used directly when it agrees
with the prescribed coefficient embedding. -/
theorem fraction_sign_with (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (baseSign : F → Int) (correct : ∀ a, baseSign a = (SignType.sign (embedding a) : Int))
    (fraction : Hex.RationalFn F) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ((HexPolyTheory.toPolynomial fraction.den).map embedding).eval t ≠ 0 ∧
      (SignType.sign (evalMapped embedding fraction t) : Int) =
        Hex.OrderedFn.Infinitesimal.sign baseSign fraction := by
  have same : baseSign = Hex.OrderedFn.orderSign := by
    funext a
    simpa only [ordered.sign_comp, Hex.OrderedFn.Infinitesimal.orderSign_eq] using correct a
  simpa only [same] using fraction_sign_map embedding ordered fraction

/-- The actual predecessor sign is preserved on one common neighborhood for
all finitely recorded fractions and denominator guards. -/
theorem finite_fractions_with (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (baseSign : F → Int) (correct : ∀ a, baseSign a = (SignType.sign (embedding a) : Int))
    (fractions : Finset (Hex.RationalFn F)) :
    ∃ η > (0 : ℝ), ∀ t, 0 < t → t < η → ∀ fraction ∈ fractions,
      ((HexPolyTheory.toPolynomial fraction.den).map embedding).eval t ≠ 0 ∧
      (SignType.sign (evalMapped embedding fraction t) : Int) =
        Hex.OrderedFn.Infinitesimal.sign baseSign fraction := by
  have stable := (eventually_all_finset fractions).mpr
    fun fraction _ => fraction_sign_with embedding ordered baseSign correct fraction
  obtain ⟨η, positive, holds⟩ := Metric.mem_nhdsWithin_iff.mp stable
  refine ⟨η, positive, fun t ht hη => holds ?_⟩
  exact ⟨by simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ht] using hη, ht⟩

/-- One ordinary parameter realizes all signs from the actual predecessor
sign function, with all denominator guards, below a positive cap. -/
theorem exists_parameter_with (embedding : F →+* ℝ) (ordered : StrictMono embedding)
    (baseSign : F → Int) (correct : ∀ a, baseSign a = (SignType.sign (embedding a) : Int))
    (fractions : Finset (Hex.RationalFn F)) (cap : ℝ) (positive : 0 < cap) :
    ∃ t : ℝ, 0 < t ∧ t < cap ∧ ∀ fraction ∈ fractions,
      ((HexPolyTheory.toPolynomial fraction.den).map embedding).eval t ≠ 0 ∧
      (SignType.sign (evalMapped embedding fraction t) : Int) =
        Hex.OrderedFn.Infinitesimal.sign baseSign fraction := by
  have stable := (eventually_all_finset fractions).mpr
    fun fraction _ => fraction_sign_with embedding ordered baseSign correct fraction
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

/-- info: 'Hex.RealClosure.Specialize.evalMapped_eq_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.evalMapped_eq_eval

/-- info: 'Hex.RealClosure.Specialize.evalMapped_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.evalMapped_add

/-- info: 'Hex.RealClosure.Specialize.evalMapped_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.evalMapped_mul

/-- info: 'Hex.RealClosure.Specialize.fraction_sign_with' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.fraction_sign_with

/-- info: 'Hex.RealClosure.Specialize.finite_fractions_with' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.finite_fractions_with

/-- info: 'Hex.RealClosure.Specialize.exists_parameter_with' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.exists_parameter_with

/-- info: 'Hex.RealClosure.Specialize.evalMapped_ofPoly' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.evalMapped_ofPoly

/-- info: 'Hex.RealClosure.Specialize.evalMapped_C' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.evalMapped_C

/-- info: 'Hex.RealClosure.Specialize.evalMapped_X' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.evalMapped_X

/-- info: 'Hex.RealClosure.Specialize.evalMapped_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.evalMapped_zero

/-- info: 'Hex.RealClosure.Specialize.evalMapped_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.evalMapped_one

/-- info: 'Hex.RealClosure.Specialize.evalMapped_nat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.evalMapped_nat

/-- info: 'Hex.RealClosure.Specialize.evalMapped_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.evalMapped_neg

/-- info: 'Hex.RealClosure.Specialize.evalMapped_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.evalMapped_sub

/-- info: 'Hex.RealClosure.Specialize.evalMapped_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.evalMapped_inv

/-- info: 'Hex.RealClosure.Specialize.evalMapped_div' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.evalMapped_div

/-- info: 'Hex.RealClosure.Specialize.evalMapped_int' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.evalMapped_int

/-- info: 'Hex.RealClosure.Specialize.evalMapped_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.evalMapped_pow
