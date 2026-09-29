/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.SpecializeRegular
public import HexRealRoots.Tarski

public section

namespace Hex.RealClosure.Specialize
attribute [local instance 2000] Field.toGrindField

private theorem subIsZero_eq {K : Type} [Field K] [DecidableEq K]
    (p q : Hex.DensePoly K) :
    Hex.SignedRemainderChain.subIsZero p q = true ↔
      HexPolyMathlib.toPolynomial p = HexPolyMathlib.toPolynomial q := by
  rw [Hex.SignedRemainderChain.subIsZero, Hex.DensePoly.isZero_eq_true_iff,
    Hex.DensePoly.size_eq_zero_iff]
  constructor
  · intro zero
    have zero := congrArg (HexPolyMathlib.toPolynomial (R := K)) zero
    rw [HexPolyMathlib.toPolynomial_sub, HexPolyMathlib.toPolynomial_zero] at zero
    exact sub_eq_zero.mp zero
  · intro equal
    apply (HexPolyMathlib.equiv (R := K)).injective
    change HexPolyMathlib.toPolynomial _ = HexPolyMathlib.toPolynomial _
    rw [HexPolyMathlib.toPolynomial_sub, HexPolyMathlib.toPolynomial_zero, equal, sub_self]

end Hex.RealClosure.Specialize

namespace Hex.RemainderStep
open RealClosure.Specialize
attribute [local instance 2000] Field.toGrindField

variable {F : Type} [Field F] [DecidableEq F]

/-- Substitute the actual stored scalar and quotient data of one remainder
step, retaining its supplied recurrence rather than recomputing division. -/
@[expose] noncomputable def specialize (embedding : F →+* ℝ) (t : ℝ)
    (step : RemainderStep (RationalFn F)) : RemainderStep ℝ := by
  classical
  exact ⟨evalMapped embedding step.leftScale t, polynomial embedding step.quotient t,
    evalMapped embedding step.rightScale t⟩

/-- An accepted signed recurrence remains accepted after finite regular
coefficient substitution and preservation of its two recorded scale signs. -/
theorem check_specialize (embedding : F →+* ℝ) (t : ℝ)
    (sign : RationalFn F → Int) (a b c : DensePoly (RationalFn F))
    (step : RemainderStep (RationalFn F))
    (ha : ∀ i < a.size, Regular embedding t (a.coeff i))
    (hb : ∀ i < b.size, Regular embedding t (b.coeff i))
    (hc : ∀ i < c.size, Regular embedding t (c.coeff i))
    (hq : ∀ i < step.quotient.size, Regular embedding t (step.quotient.coeff i))
    (hl : Regular embedding t step.leftScale) (hr : Regular embedding t step.rightScale)
    (sl : (SignType.sign (evalMapped embedding step.leftScale t) : Int) = sign step.leftScale)
    (sr : (SignType.sign (evalMapped embedding step.rightScale t) : Int) = sign step.rightScale)
    (accepted : SignedRemainderChain.checkStep sign a b c step = true) :
    SignedRemainderChain.checkStep (fun x : ℝ => (SignType.sign x : Int))
      (polynomial embedding a t) (polynomial embedding b t) (polynomial embedding c t)
      (step.specialize embedding t) = true := by
  classical
  simp only [SignedRemainderChain.checkStep, Bool.and_eq_true, decide_eq_true_eq,
    and_assoc] at accepted ⊢
  refine ⟨?_, ?_, ?_⟩
  · simpa only [specialize, sl] using accepted.1
  · simpa only [specialize, sr] using accepted.2.1
  · obtain ⟨A, hA⟩ := polynomial_lift embedding t a ha
    obtain ⟨B, hB⟩ := polynomial_lift embedding t b hb
    obtain ⟨C, hC⟩ := polynomial_lift embedding t c hc
    obtain ⟨Q, hQ⟩ := polynomial_lift embedding t step.quotient hq
    have native := (RealClosure.Specialize.subIsZero_eq _ _).mp accepted.2.2
    have lifted : Polynomial.C (⟨step.leftScale, hl⟩ : regularRing embedding t) * A =
        Q * B - Polynomial.C (⟨step.rightScale, hr⟩ : regularRing embedding t) * C := by
      apply Polynomial.map_injective (regularRing embedding t).subtype Subtype.val_injective
      rw [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul,
        Polynomial.map_C, Polynomial.map_C, hA, hB, hC, hQ]
      simpa only [Subring.subtype_apply, Subtype.coe_mk, HexPolyMathlib.toPolynomial_scale,
        HexPolyMathlib.toPolynomial_mul, HexPolyMathlib.toPolynomial_sub] using native
    have evaluated := congrArg (Polynomial.map (evaluation embedding t)) lifted
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C] at evaluated
    have left : evaluation embedding t (⟨step.leftScale, hl⟩ : regularRing embedding t) =
        evalMapped embedding step.leftScale t := rfl
    have right : evaluation embedding t (⟨step.rightScale, hr⟩ : regularRing embedding t) =
        evalMapped embedding step.rightScale t := rfl
    rw [left, right] at evaluated
    apply (RealClosure.Specialize.subIsZero_eq _ _).mpr
    simpa only [specialize, HexPolyMathlib.toPolynomial_scale, HexPolyMathlib.toPolynomial_mul,
      HexPolyMathlib.toPolynomial_sub, polynomial_map embedding t a A hA,
      polynomial_map embedding t b B hB, polynomial_map embedding t c C hC,
      polynomial_map embedding t step.quotient Q hQ] using evaluated

/-- The finite native fraction data needed by the step's local substitution. -/
@[expose] noncomputable def fractions (step : RemainderStep (RationalFn F)) :
    Finset (RationalFn F) := by
  classical
  exact step.quotient.toArray.toList.toFinset ∪ {step.leftScale, step.rightScale}

/-- info: 'Hex.RemainderStep.check_specialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RemainderStep.check_specialize

end Hex.RemainderStep

namespace Hex.SignedRemainderChain
open RealClosure.Specialize
attribute [local instance 2000] Field.toGrindField

variable {F : Type} [Field F] [DecidableEq F]

/-- Substitute the literal chain entries, quotients and scales, retaining
serialized degrees for subsequent checking. No producer or division runs. -/
@[expose] noncomputable def specialize (embedding : F →+* ℝ) (t : ℝ)
    (cert : SignedRemainderChain (RationalFn F)) : SignedRemainderChain ℝ := by
  classical
  exact {
    chain := cert.chain.map (fun p => polynomial embedding p t)
    degrees := cert.degrees
    initial := cert.initial.specialize embedding t
    steps := cert.steps.map (fun step => step.specialize embedding t)
    terminal := cert.terminal.map (fun pair =>
      (evalMapped embedding pair.1 t, polynomial embedding pair.2 t)) }

/-- All literal fraction coefficients and scales in the supplied chain.
This finite family supplies regularity and degree/zero preservation for its
stored polynomials; endpoint evaluation signs are separate query obligations. -/
@[expose] noncomputable def fractions (cert : SignedRemainderChain (RationalFn F)) :
    Finset (RationalFn F) := by
  classical
  exact (cert.chain.toList.flatMap (fun p => p.toArray.toList)).toFinset ∪
    cert.initial.fractions ∪
    (cert.steps.toList.flatMap (fun step => step.fractions.toList)).toFinset ∪
    (cert.terminal.toList.flatMap (fun pair => pair.1 :: pair.2.toArray.toList)).toFinset

end Hex.SignedRemainderChain

