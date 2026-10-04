/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.SpecializeNested
public import HexPolyMathlib.GrindTransport

public section

namespace Hex.RealClosure.Specialize

attribute [local instance 2000] Field.toGrindField
attribute [local instance] HexPolyMathlib.denseCommRing

variable {F G : Type} [Field F] [DecidableEq F] [Field G] [DecidableEq G]

/-- Polynomial substitution on a coefficient subring, expressed in the native
dense-polynomial representation. -/
noncomputable def nativeMap {S : Type} [CommRing S] (hom : S →+* F) :
    Polynomial S →+* Hex.DensePoly F :=
  (HexPolyMathlib.equiv (R := F)).symm.toRingHom.comp (Polynomial.mapRingHom hom)

theorem nativeMap_toPolynomial {S : Type} [CommRing S] (hom : S →+* F)
    (p : Polynomial S) : HexPolyMathlib.toPolynomial (nativeMap hom p) = p.map hom :=
  (HexPolyMathlib.equiv (R := F)).apply_symm_apply _

/-- A fraction has a presentation over the coefficient subring whose
denominator survives the prescribed substitution. Canonical coefficients need
not belong to that subring. -/
structure FractionPresentation (domain : Subring F) (value : domain →+* G)
    (fraction : Hex.RationalFn F) where
  num : Polynomial domain
  den : Polynomial domain
  represents : Hex.RationalFn.Represents fraction
    (nativeMap domain.subtype num) (nativeMap domain.subtype den)
  nonzero : nativeMap value den ≠ 0

namespace FractionPresentation

variable {domain : Subring F} {value : domain →+* G} {fraction : Hex.RationalFn F}

/-- Substitute this actual fraction presentation and normalize its surviving
denominator using the ordinary native rational-function constructor. -/
noncomputable def eval (presentation : FractionPresentation domain value fraction) :
    Hex.RationalFn G :=
  Hex.RationalFn.normalize (nativeMap value presentation.num)
    (nativeMap value presentation.den) presentation.nonzero

theorem eval_spec (presentation : FractionPresentation domain value fraction) :
    Hex.RationalFn.Represents presentation.eval (nativeMap value presentation.num)
      (nativeMap value presentation.den) :=
  Hex.RationalFn.normalize_spec _ _ presentation.nonzero

private theorem source_injective : Function.Injective (nativeMap domain.subtype) := by
  apply Function.Injective.comp (HexPolyMathlib.equiv (R := F)).symm.injective
  exact Polynomial.map_injective domain.subtype domain.subtype_injective

/-- The source fraction determines the cross-product identity in the
coefficient subring itself. -/
theorem cross (first second : FractionPresentation domain value fraction) :
    first.num * second.den = second.num * first.den := by
  apply source_injective
  simp only [map_mul]
  apply Hex.DensePoly.mul_right_cancel fraction.den_ne_zero
  have left := first.represents
  have right := second.represents
  unfold Hex.RationalFn.Represents at left right
  grind

/-- Substitution is independent of the presentation, even when the
coefficient substitution kills a nonzero source numerator. -/
theorem eval_eq (first second : FractionPresentation domain value fraction) :
    first.eval = second.eval := by
  apply (Hex.RationalFn.eq_iff _ _).mpr
  apply Hex.DensePoly.mul_right_cancel
    (Hex.DensePoly.mul_ne_zero first.nonzero second.nonzero)
  have left := first.eval_spec
  have right := second.eval_spec
  have equation := congrArg (nativeMap value) (first.cross second)
  simp only [map_mul] at equation
  unfold Hex.RationalFn.Represents at left right
  grind

noncomputable def zero (domain : Subring F) (value : domain →+* G) :
    FractionPresentation domain value 0 where
  num := 0
  den := 1
  represents := by
    change 0 * nativeMap domain.subtype 1 = nativeMap domain.subtype 0 * 1
    rw [map_one, map_zero]
  nonzero := by
    rw [map_one]
    exact Hex.DensePoly.monic_ne_zero Hex.DensePoly.monic_one

noncomputable def one (domain : Subring F) (value : domain →+* G) :
    FractionPresentation domain value 1 where
  num := 1
  den := 1
  represents := by
    change 1 * nativeMap domain.subtype 1 = nativeMap domain.subtype 1 * 1
    rw [map_one]
  nonzero := by
    rw [map_one]
    exact Hex.DensePoly.monic_ne_zero Hex.DensePoly.monic_one

noncomputable def add {first second : Hex.RationalFn F}
    (left : FractionPresentation domain value first)
    (right : FractionPresentation domain value second) :
    FractionPresentation domain value (first + second) where
  num := left.num * right.den + right.num * left.den
  den := left.den * right.den
  represents := by
    simpa only [map_add, map_mul] using left.represents.add right.represents
  nonzero := by
    rw [map_mul]
    exact Hex.DensePoly.mul_ne_zero left.nonzero right.nonzero

noncomputable def mul {first second : Hex.RationalFn F}
    (left : FractionPresentation domain value first)
    (right : FractionPresentation domain value second) :
    FractionPresentation domain value (first * second) where
  num := left.num * right.num
  den := left.den * right.den
  represents := by
    simpa only [map_mul] using left.represents.mul right.represents
  nonzero := by
    rw [map_mul]
    exact Hex.DensePoly.mul_ne_zero left.nonzero right.nonzero

noncomputable def neg (presentation : FractionPresentation domain value fraction) :
    FractionPresentation domain value (-fraction) where
  num := -presentation.num
  den := presentation.den
  represents := by
    simpa only [map_neg] using presentation.represents.neg
  nonzero := presentation.nonzero

theorem eval_zero (domain : Subring F) (value : domain →+* G) :
    (zero domain value).eval = 0 := by
  apply (zero domain value).eval_spec.eq _ (zero domain value).nonzero
  change 0 * nativeMap value 1 = nativeMap value 0 * 1
  rw [map_one, map_zero]

theorem eval_one (domain : Subring F) (value : domain →+* G) :
    (one domain value).eval = 1 := by
  apply (one domain value).eval_spec.eq _ (one domain value).nonzero
  change 1 * nativeMap value 1 = nativeMap value 1 * 1
  rw [map_one]

theorem eval_add {first second : Hex.RationalFn F}
    (left : FractionPresentation domain value first)
    (right : FractionPresentation domain value second) :
    (left.add right).eval = left.eval + right.eval := by
  apply (left.add right).eval_spec.eq _ (left.add right).nonzero
  simpa only [add, map_mul, map_add] using left.eval_spec.add right.eval_spec

theorem eval_mul {first second : Hex.RationalFn F}
    (left : FractionPresentation domain value first)
    (right : FractionPresentation domain value second) :
    (left.mul right).eval = left.eval * right.eval := by
  apply (left.mul right).eval_spec.eq _ (left.mul right).nonzero
  simpa only [mul, map_mul] using left.eval_spec.mul right.eval_spec

theorem eval_neg (presentation : FractionPresentation domain value fraction) :
    presentation.neg.eval = -presentation.eval := by
  apply presentation.neg.eval_spec.eq _ presentation.neg.nonzero
  simpa only [neg, map_neg] using presentation.eval_spec.neg

end FractionPresentation

/-- Fractions admitting a presentation with a surviving substituted
denominator form a ring. This permits intermediate polynomial arithmetic
without requiring regular canonical coefficients at every intermediate step. -/
noncomputable def fractionRing (domain : Subring F) (value : domain →+* G) :
    Subring (Hex.RationalFn F) where
  carrier := fun fraction => Nonempty (FractionPresentation domain value fraction)
  zero_mem' := ⟨FractionPresentation.zero domain value⟩
  one_mem' := ⟨FractionPresentation.one domain value⟩
  add_mem' := by
    rintro _ _ ⟨left⟩ ⟨right⟩
    exact ⟨left.add right⟩
  mul_mem' := by
    rintro _ _ ⟨left⟩ ⟨right⟩
    exact ⟨left.mul right⟩
  neg_mem' := by
    rintro _ ⟨presentation⟩
    exact ⟨presentation.neg⟩

namespace FractionRing

variable (domain : Subring F) (value : domain →+* G)

private noncomputable def chosen (fraction : fractionRing domain value) :
    FractionPresentation domain value fraction.val :=
  Classical.choice fraction.property

/-- Coefficient substitution is a ring homomorphism on fractions that admit
surviving presentations. Presentation independence fixes its actual value. -/
noncomputable def evaluation : fractionRing domain value →+* Hex.RationalFn G where
  toFun := fun fraction => (chosen domain value fraction).eval
  map_zero' := by
    exact ((chosen domain value 0).eval_eq (FractionPresentation.zero domain value)).trans
      (FractionPresentation.eval_zero domain value)
  map_one' := by
    exact ((chosen domain value 1).eval_eq (FractionPresentation.one domain value)).trans
      (FractionPresentation.eval_one domain value)
  map_add' := by
    intro first second
    exact ((chosen domain value (first + second)).eval_eq
      ((chosen domain value first).add (chosen domain value second))).trans
        ((chosen domain value first).eval_add (chosen domain value second))
  map_mul' := by
    intro first second
    exact ((chosen domain value (first * second)).eval_eq
      ((chosen domain value first).mul (chosen domain value second))).trans
        ((chosen domain value first).eval_mul (chosen domain value second))

/-- Every presentation of a ring member evaluates to this homomorphism's
value, independently of its membership witness. -/
theorem evaluation_eq (fraction : fractionRing domain value)
    (presentation : FractionPresentation domain value fraction.val) :
    evaluation domain value fraction = presentation.eval :=
  (chosen domain value fraction).eval_eq presentation

end FractionRing

/-- Finite guards on the stored inner coefficients provide a genuine member
of the substitution ring. Its homomorphic value is the native first-parameter
substitution, with the remaining indeterminate still symbolic. -/
theorem mapFraction_mem (fraction : Hex.RationalFn (Hex.RationalFn ℝ)) (first : ℝ)
    (num : CoefficientData (HexPolyMathlib.toPolynomial fraction.num) first)
    (den : CoefficientData (HexPolyMathlib.toPolynomial fraction.den) first) :
    ∃ member : fraction ∈ fractionRing (regularRing (RingHom.id ℝ) first)
        (evaluation (RingHom.id ℝ) first),
      FractionRing.evaluation (regularRing (RingHom.id ℝ) first)
        (evaluation (RingHom.id ℝ) first) ⟨fraction, member⟩ = mapFraction fraction first := by
  classical
  have regular (p : Hex.DensePoly (Hex.RationalFn ℝ))
      (data : CoefficientData (HexPolyMathlib.toPolynomial p) first) (i : Nat) :
      Regular (RingHom.id ℝ) first (p.coeff i) := by
    have reflect : evalMapped (RingHom.id ℝ) (p.coeff i) first = 0 ↔ p.coeff i = 0 := by
      simpa only [evalMapped, evalFraction, Polynomial.map_id,
        HexPolyMathlib.coeff_toPolynomial] using data.zero_iff i
    by_cases zero : p.coeff i = 0
    · rw [zero]
      exact (regularRing (RingHom.id ℝ) first).zero_mem
    · intro vanishes
      apply zero
      apply reflect.mp
      simp only [evalMapped, vanishes, div_zero]
  obtain ⟨N, hn⟩ := polynomial_lift (RingHom.id ℝ) first fraction.num
    (fun i _ => regular fraction.num num i)
  obtain ⟨D, hd⟩ := polynomial_lift (RingHom.id ℝ) first fraction.den
    (fun i _ => regular fraction.den den i)
  have sourceNum : nativeMap (regularRing (RingHom.id ℝ) first).subtype N = fraction.num := by
    apply (HexPolyMathlib.equiv (R := Hex.RationalFn ℝ)).injective
    exact (nativeMap_toPolynomial _ _).trans hn
  have sourceDen : nativeMap (regularRing (RingHom.id ℝ) first).subtype D = fraction.den := by
    apply (HexPolyMathlib.equiv (R := Hex.RationalFn ℝ)).injective
    exact (nativeMap_toPolynomial _ _).trans hd
  have targetNum : nativeMap (evaluation (RingHom.id ℝ) first) N =
      polynomial (RingHom.id ℝ) fraction.num first := by
    apply (HexPolyMathlib.equiv (R := ℝ)).injective
    exact (nativeMap_toPolynomial _ _).trans (polynomial_map _ _ _ _ hn).symm
  have targetDen : nativeMap (evaluation (RingHom.id ℝ) first) D =
      polynomial (RingHom.id ℝ) fraction.den first := by
    apply (HexPolyMathlib.equiv (R := ℝ)).injective
    exact (nativeMap_toPolynomial _ _).trans (polynomial_map _ _ _ _ hd).symm
  have nonzero : nativeMap (evaluation (RingHom.id ℝ) first) D ≠ 0 := by
    rw [targetDen]
    apply (polynomial_zero (RingHom.id ℝ) fraction.den first (fun i _ => ?_)).not.mpr
      fraction.den_ne_zero
    simpa only [evalMapped, evalFraction, Polynomial.map_id, HexPolyMathlib.coeff_toPolynomial]
      using den.zero_iff i
  let presentation : FractionPresentation (regularRing (RingHom.id ℝ) first)
      (evaluation (RingHom.id ℝ) first) fraction := {
    num := N
    den := D
    represents := by rw [sourceNum, sourceDen]; exact Hex.RationalFn.represents_self fraction
    nonzero }
  have member : fraction ∈ fractionRing (regularRing (RingHom.id ℝ) first)
      (evaluation (RingHom.id ℝ) first) := ⟨presentation⟩
  refine ⟨member, ?_⟩
  rw [FractionRing.evaluation_eq _ _ _ presentation]
  apply presentation.eval_spec.eq _ nonzero
  change Hex.RationalFn.Represents (mapFraction fraction first)
    (nativeMap (evaluation (RingHom.id ℝ) first) N)
    (nativeMap (evaluation (RingHom.id ℝ) first) D)
  rw [targetNum, targetDen]
  exact mapFraction_spec fraction first den

end Hex.RealClosure.Specialize

/-- info: 'Hex.RealClosure.Specialize.FractionPresentation.eval_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.FractionPresentation.eval_eq

/-- info: 'Hex.RealClosure.Specialize.FractionRing.evaluation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.FractionRing.evaluation

/-- info: 'Hex.RealClosure.Specialize.mapFraction_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.mapFraction_mem
