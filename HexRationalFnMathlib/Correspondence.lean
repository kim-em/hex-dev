/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRationalFn
public import HexPolyMathlib
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.Algebra.Field.MinimalAxioms
public import Mathlib.Tactic.FieldSimp

public section

namespace HexRationalFnMathlib

universe u
variable {K : Type u} [Field K] [DecidableEq K]
open Hex

/-- Mathlib field laws on the executable operations, powers, and casts. -/
noncomputable instance field : Field (RationalFn K) :=
  { Field.ofMinimalAxioms (RationalFn K)
      RationalFn.add_assoc
      (fun f => (RationalFn.add_comm 0 f).trans (RationalFn.add_zero f))
      RationalFn.neg_add_cancel RationalFn.mul_assoc RationalFn.mul_comm
      (fun f => (RationalFn.mul_comm 1 f).trans (RationalFn.mul_one f))
      (fun _ h => RationalFn.mul_inv_cancel h) RationalFn.inv_zero
      RationalFn.left_distrib ⟨0, 1, RationalFn.zero_ne_one⟩ with
    nsmul := fun n f => (Nat.cast n : RationalFn K) * f
    nsmul_zero := fun f => by
      change (0 : RationalFn K) * f = 0
      exact RationalFn.zero_mul f
    nsmul_succ := fun n f => by
      change (Nat.cast (n + 1) : RationalFn K) * f = Nat.cast n * f + f
      rw [Lean.Grind.Semiring.natCast_succ, Lean.Grind.Semiring.right_distrib,
        Lean.Grind.Semiring.one_mul]
    zsmul := fun n f => (Int.cast n : RationalFn K) * f
    zsmul_zero' := fun f => by
      change (0 : RationalFn K) * f = 0
      exact RationalFn.zero_mul f
    zsmul_succ' := fun n f => by
      change (Int.cast ((n + 1 : Nat) : Int) : RationalFn K) * f =
        Int.cast (n : Int) * f + f
      rw [Lean.Grind.Ring.intCast_natCast, Lean.Grind.Ring.intCast_natCast,
        Lean.Grind.Semiring.natCast_succ, Lean.Grind.Semiring.right_distrib,
        Lean.Grind.Semiring.one_mul]
    zsmul_neg' := fun n f => by
      exact Lean.Grind.Ring.neg_zsmul ((n + 1 : Nat) : Int) f
    npow := fun n f => RationalFn.powWith RationalFn.defaultPlan f n
    npow_zero := RationalFn.pow_zero
    npow_succ := fun n f => RationalFn.pow_succ f n
    zpow := fun n f => f ^ n
    zpow_zero' := fun f => Lean.Grind.Field.zpow_zero f
    zpow_succ' := fun n f => Lean.Grind.Field.zpow_succ f n
    zpow_neg' := fun _ _ => rfl
    natCast := fun n => RationalFn.ofPoly (Nat.cast n)
    natCast_zero := rfl
    natCast_succ := fun n => Lean.Grind.Semiring.natCast_succ n
    intCast := fun n => RationalFn.ofPoly (Int.cast n)
    intCast_ofNat := fun n => Lean.Grind.Ring.intCast_natCast n
    intCast_negSucc := fun n => by
      change RationalFn.ofPoly (Int.cast (-(n + 1 : Int))) =
        -(RationalFn.ofPoly (Nat.cast (n + 1)))
      rw [Lean.Grind.Ring.intCast_neg]
      have hn : (n : Int) + 1 = ((n + 1 : Nat) : Int) := by omega
      rw [hn, Lean.Grind.Ring.intCast_natCast, RationalFn.ofPoly_neg]
    nnratCast := fun q => (Nat.cast q.num : RationalFn K) / Nat.cast q.den
    nnratCast_def := fun _ => rfl
    ratCast := fun q => (Int.cast q.num : RationalFn K) / Nat.cast q.den
    ratCast_def := fun _ => rfl
    nnqsmul := fun q f => ((Nat.cast q.num : RationalFn K) / Nat.cast q.den) * f
    nnqsmul_def := fun _ _ => rfl
    qsmul := fun q f => ((Int.cast q.num : RationalFn K) / Nat.cast q.den) * f
    qsmul_def := fun _ _ => rfl }

noncomputable section

/-- Embed a dense polynomial into Mathlib's rational-function field. -/
def embed (p : DensePoly K) : RatFunc K :=
  algebraMap (Polynomial K) (RatFunc K) (HexPolyMathlib.toPolynomial p)

@[simp] theorem embed_zero : embed (0 : DensePoly K) = 0 := by simp [embed]
@[simp] theorem embed_one : embed (1 : DensePoly K) = 1 := by simp [embed]
@[simp] theorem embed_add (p q : DensePoly K) : embed (p + q) = embed p + embed q := by simp [embed]
@[simp] theorem embed_mul (p q : DensePoly K) : embed (p * q) = embed p * embed q := by simp [embed]

/-- Dense polynomial embedding into the fraction field is injective. -/
theorem embed_injective : Function.Injective (embed (K := K)) :=
  (RatFunc.algebraMap_injective K).comp HexPolyMathlib.equiv.injective

/-- Nonzero dense polynomials remain nonzero in the fraction field. -/
theorem embed_ne_zero {p : DensePoly K} (hp : p ≠ 0) : embed p ≠ 0 := by
  intro h
  apply hp
  exact embed_injective (h.trans embed_zero.symm)

/-- Interpret the stored canonical fraction in Mathlib. -/
@[expose]
def toRatFunc (f : RationalFn K) : RatFunc K := embed f.num / embed f.den

/-- Interpretation respects any fraction presentation. -/
theorem toRatFunc_eq {f : RationalFn K} {p q : DensePoly K}
    (h : RationalFn.Represents f p q) (hq : q ≠ 0) :
    toRatFunc f = embed p / embed q := by
  apply (div_eq_div_iff (embed_ne_zero f.den_ne_zero) (embed_ne_zero hq)).mpr
  simpa only [embed_mul] using congrArg embed h

/-- Equal interpretations force equal canonical coefficient arrays. -/
theorem toRatFunc_injective : Function.Injective (toRatFunc (K := K)) := by
  intro f g h
  apply (RationalFn.eq_iff f g).mpr
  apply embed_injective
  simpa only [embed_mul] using
    (div_eq_div_iff (embed_ne_zero f.den_ne_zero) (embed_ne_zero g.den_ne_zero)).mp h

/-- The monicity invariant transports to Mathlib polynomials. -/
theorem monic_den (f : RationalFn K) : (HexPolyMathlib.toPolynomial f.den).Monic := by
  change (HexPolyMathlib.toPolynomial f.den).leadingCoeff = 1
  rw [HexPolyMathlib.leadingCoeff_toPolynomial]
  exact f.monic_den

/-- Build the executable canonical pair of a mathematical rational function. -/
def fromRatFunc (f : RatFunc K) : RationalFn K :=
  RationalFn.ofCoprime (HexPolyMathlib.ofPolynomial f.num) (HexPolyMathlib.ofPolynomial f.denom)
    (by
      have h := HexPolyMathlib.leadingCoeff_toPolynomial (HexPolyMathlib.ofPolynomial f.denom)
      rw [HexPolyMathlib.toPolynomial_ofPolynomial] at h
      change (HexPolyMathlib.ofPolynomial f.denom).leadingCoeff = 1
      rw [← h]
      exact f.monic_denom)
    (by
      obtain ⟨s, t, h⟩ := f.isCoprime_num_denom
      refine ⟨HexPolyMathlib.ofPolynomial s, HexPolyMathlib.ofPolynomial t, ?_⟩
      apply HexPolyMathlib.equiv.injective
      simpa only [map_add, map_mul, map_one, HexPolyMathlib.equiv_apply,
        HexPolyMathlib.toPolynomial_ofPolynomial, HexPolyMathlib.toPolynomial_one] using h)

/-- The mathematical inverse presentation recovers its input fraction. -/
@[simp]
theorem to_from (f : RatFunc K) : toRatFunc (fromRatFunc f) = f := by
  change algebraMap (Polynomial K) (RatFunc K)
      (HexPolyMathlib.toPolynomial (HexPolyMathlib.ofPolynomial f.num)) /
    algebraMap (Polynomial K) (RatFunc K)
      (HexPolyMathlib.toPolynomial (HexPolyMathlib.ofPolynomial f.denom)) = f
  rw [HexPolyMathlib.toPolynomial_ofPolynomial, HexPolyMathlib.toPolynomial_ofPolynomial,
    RatFunc.num_div_denom]

/-- Recovering canonical polynomials from the interpretation gives the stored value. -/
@[simp]
theorem from_to (f : RationalFn K) : fromRatFunc (toRatFunc f) = f :=
  toRatFunc_injective (to_from _)

/-- The stored numerator agrees with Mathlib's canonical numerator. -/
theorem num_toRatFunc (f : RationalFn K) :
    HexPolyMathlib.toPolynomial f.num = (toRatFunc f).num := by
  have h := congrArg (fun g : RationalFn K => HexPolyMathlib.toPolynomial g.num) (from_to f)
  change HexPolyMathlib.toPolynomial (HexPolyMathlib.ofPolynomial (toRatFunc f).num) =
    HexPolyMathlib.toPolynomial f.num at h
  rw [HexPolyMathlib.toPolynomial_ofPolynomial] at h
  exact h.symm

/-- The stored denominator agrees with Mathlib's canonical monic denominator. -/
theorem den_toRatFunc (f : RationalFn K) :
    HexPolyMathlib.toPolynomial f.den = (toRatFunc f).denom := by
  have h := congrArg (fun g : RationalFn K => HexPolyMathlib.toPolynomial g.den) (from_to f)
  change HexPolyMathlib.toPolynomial (HexPolyMathlib.ofPolynomial (toRatFunc f).denom) =
    HexPolyMathlib.toPolynomial f.den at h
  rw [HexPolyMathlib.toPolynomial_ofPolynomial] at h
  exact h.symm

/-- Polynomial embedding has its mathematical interpretation. -/
@[simp]
theorem toRatFunc_ofPoly (p : DensePoly K) : toRatFunc (RationalFn.ofPoly p) = embed p := by
  change embed p / embed 1 = embed p
  simp

/-- Interpretation preserves addition. -/
@[simp]
theorem toRatFunc_add (f g : RationalFn K) : toRatFunc (f + g) = toRatFunc f + toRatFunc g := by
  rw [toRatFunc_eq (RationalFn.add_spec f g) (DensePoly.mul_ne_zero f.den_ne_zero g.den_ne_zero)]
  simp only [embed_add, embed_mul, toRatFunc]
  simpa only [mul_comm] using
    (div_add_div (embed f.num) (embed g.num) (embed_ne_zero f.den_ne_zero) (embed_ne_zero g.den_ne_zero)).symm

/-- Interpretation preserves multiplication. -/
@[simp]
theorem toRatFunc_mul (f g : RationalFn K) : toRatFunc (f * g) = toRatFunc f * toRatFunc g := by
  rw [toRatFunc_eq (RationalFn.mul_spec f g) (DensePoly.mul_ne_zero f.den_ne_zero g.den_ne_zero)]
  simp only [embed_mul, toRatFunc]
  exact (div_mul_div_comm _ _ _ _).symm

/-- The executable canonical field is ring-equivalent to Mathlib rational functions. -/
@[expose]
def equiv : RationalFn K ≃+* RatFunc K where
  toFun := toRatFunc
  invFun := fromRatFunc
  left_inv := from_to
  right_inv := to_from
  map_add' := toRatFunc_add
  map_mul' := toRatFunc_mul

/-- Interpretation preserves zero. -/
@[simp] theorem toRatFunc_zero : toRatFunc (0 : RationalFn K) = 0 := equiv.map_zero

/-- Interpretation preserves one. -/
@[simp] theorem toRatFunc_one : toRatFunc (1 : RationalFn K) = 1 :=
  (equiv (K := K)).map_one

/-- Constants map to the coefficient-field embedding. -/
@[simp]
theorem toRatFunc_C (a : K) : toRatFunc (RationalFn.C a) = algebraMap K (RatFunc K) a := by
  rw [RationalFn.C, toRatFunc_ofPoly]
  simp only [embed, HexPolyMathlib.toPolynomial_C]
  exact (IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K) a).symm

/-- The executable indeterminate maps to Mathlib's rational indeterminate. -/
@[simp]
theorem toRatFunc_X : toRatFunc (RationalFn.X : RationalFn K) = RatFunc.X := by
  rw [RationalFn.X, toRatFunc_ofPoly]
  simp [embed, HexPolyMathlib.toPolynomial_monomial, Polynomial.monomial_one_one_eq_X,
    RatFunc.algebraMap_X]

/-- The executable constant embedding as a ring homomorphism. -/
def constantHom : K →+* RationalFn K where
  toFun := RationalFn.C
  map_zero' := by
    apply RationalFn.ext
    · apply DensePoly.ext_coeff
      intro i
      change (DensePoly.C (0 : K)).coeff i = (0 : DensePoly K).coeff i
      rw [DensePoly.coeff_C, DensePoly.coeff_zero]
      split <;> rfl
    · rfl
  map_one' := rfl
  map_add' a b := by apply toRatFunc_injective; simp
  map_mul' a b := by apply toRatFunc_injective; simp

/-- Coefficients act through the executable constant embedding. -/
noncomputable instance algebra : Algebra K (RationalFn K) := constantHom.toAlgebra

/-- The same canonical correspondence as a coefficient-algebra equivalence. -/
def algEquiv : RationalFn K ≃ₐ[K] RatFunc K :=
  { equiv with commutes' := toRatFunc_C }

/-- Interpretation preserves negation. -/
@[simp] theorem toRatFunc_neg (f : RationalFn K) : toRatFunc (-f) = -toRatFunc f := equiv.map_neg f

/-- Interpretation preserves subtraction. -/
@[simp] theorem toRatFunc_sub (f g : RationalFn K) : toRatFunc (f - g) = toRatFunc f - toRatFunc g :=
  equiv.map_sub f g

/-- Interpretation preserves total inversion. -/
@[simp] theorem toRatFunc_inv (f : RationalFn K) : toRatFunc f⁻¹ = (toRatFunc f)⁻¹ := map_inv₀ equiv f

/-- Interpretation preserves total division. -/
@[simp] theorem toRatFunc_div (f g : RationalFn K) : toRatFunc (f / g) = toRatFunc f / toRatFunc g :=
  map_div₀ equiv f g

/-- Checked inversion rejects exactly the mathematical zero. -/
theorem inv?_eq_none (f : RationalFn K) :
    RationalFn.inv? f = none ↔ toRatFunc f = 0 := by
  rw [RationalFn.inv?_eq_none]
  constructor
  · intro h; subst f; exact toRatFunc_zero
  · intro h; exact toRatFunc_injective (h.trans toRatFunc_zero.symm)

/-- Checked division rejects exactly a mathematically zero divisor. -/
theorem div?_eq_none (f g : RationalFn K) :
    RationalFn.div? f g = none ↔ toRatFunc g = 0 := by
  rw [RationalFn.div?_eq_none]
  constructor
  · intro h; subst g; exact toRatFunc_zero
  · intro h; exact toRatFunc_injective (h.trans toRatFunc_zero.symm)

/-- Successful checked inversion has the mathematical inverse as its value. -/
theorem inv?_eq_some (f : RationalFn K) (hf : f ≠ 0) :
    (RationalFn.inv? f).map toRatFunc = some (toRatFunc f)⁻¹ := by
  rw [RationalFn.inv?_eq_some f hf, Option.map_some, toRatFunc_inv]

/-- Successful checked division has the mathematical quotient as its value. -/
theorem div?_eq_some (f g : RationalFn K) (hg : g ≠ 0) :
    (RationalFn.div? f g).map toRatFunc = some (toRatFunc f / toRatFunc g) := by
  rw [RationalFn.div?_eq_some f g hg, Option.map_some, toRatFunc_div]

/-- Interpretation preserves natural powers. -/
@[simp] theorem toRatFunc_pow (f : RationalFn K) (n : Nat) : toRatFunc (f ^ n) = toRatFunc f ^ n :=
  equiv.map_pow f n

/-- The derivative corresponds to the quotient rule for embedded polynomial derivatives. -/
theorem derivative_spec (f : RationalFn K) :
    toRatFunc (RationalFn.derivative f) =
      (algebraMap (Polynomial K) (RatFunc K) (HexPolyMathlib.toPolynomial f.num).derivative * embed f.den -
        embed f.num * algebraMap (Polynomial K) (RatFunc K) (HexPolyMathlib.toPolynomial f.den).derivative) /
        (embed f.den * embed f.den) := by
  rw [toRatFunc_eq (RationalFn.derivative_spec f) (DensePoly.mul_ne_zero f.den_ne_zero f.den_ne_zero)]
  simp only [embed, HexPolyMathlib.toPolynomial_sub, HexPolyMathlib.toPolynomial_mul,
    HexPolyMathlib.toPolynomial_derivative, map_sub, map_mul]

/-- Formal differentiation is additive under the correspondence. -/
theorem derivative_add (f g : RationalFn K) :
    toRatFunc (RationalFn.derivative (f + g)) =
      toRatFunc (RationalFn.derivative f) + toRatFunc (RationalFn.derivative g) := by
  rw [RationalFn.derivative_add, toRatFunc_add]

/-- Formal differentiation satisfies the Leibniz rule under the correspondence. -/
theorem derivative_mul (f g : RationalFn K) :
    toRatFunc (RationalFn.derivative (f * g)) =
      toRatFunc (RationalFn.derivative f) * toRatFunc g +
        toRatFunc f * toRatFunc (RationalFn.derivative g) := by
  rw [RationalFn.derivative_mul, toRatFunc_add, toRatFunc_mul, toRatFunc_mul]

/-- Polynomial-part decomposition agrees under the fraction-field correspondence. -/
theorem split_spec (f : RationalFn K) :
    toRatFunc f = embed (RationalFn.split f).1 + toRatFunc (RationalFn.split f).2 ∧
      RationalFn.Proper (RationalFn.split f).2 := by
  refine ⟨?_, (RationalFn.split_spec f).2⟩
  have h := congrArg toRatFunc (RationalFn.split_spec f).1
  simpa only [toRatFunc_add, toRatFunc_ofPoly] using h

/-- Polynomial recognition identifies precisely polynomial elements of the fraction field. -/
theorem toPoly?_eq_some (f : RationalFn K) (p : DensePoly K) :
    RationalFn.toPoly? f = some p ↔ toRatFunc f = embed p := by
  rw [RationalFn.toPoly?_eq_some, ← toRatFunc_ofPoly p]
  exact toRatFunc_injective.eq_iff.symm

/-- Normalization identifies both the represented fraction and its canonical components. -/
theorem normalize_spec (p q : DensePoly K) (hq : q ≠ 0) :
    let f := RationalFn.normalize p q hq
    toRatFunc f = embed p / embed q ∧
      HexPolyMathlib.toPolynomial f.num = (toRatFunc f).num ∧
      HexPolyMathlib.toPolynomial f.den = (toRatFunc f).denom :=
  ⟨toRatFunc_eq (RationalFn.normalize_spec p q hq) hq, num_toRatFunc _, den_toRatFunc _⟩

/-- The headline normalization theorem also holds for any lawful multiplication plan. -/
theorem normalizeWith_spec (plan : DensePoly.MulPlan K) (p q : DensePoly K) (hq : q ≠ 0) :
    let f := RationalFn.normalizeWith plan p q hq
    toRatFunc f = embed p / embed q ∧
      HexPolyMathlib.toPolynomial f.num = (toRatFunc f).num ∧
      HexPolyMathlib.toPolynomial f.den = (toRatFunc f).denom :=
  ⟨toRatFunc_eq (RationalFn.normalizeWith_spec plan p q hq) hq, num_toRatFunc _, den_toRatFunc _⟩

/-- Accepted certificates prove fraction and canonical-component agreement without search replay. -/
theorem check_sound (p q : DensePoly K) (cert : RationalFn.Cert K)
    (h : RationalFn.check p q cert = true) :
    let f := RationalFn.ofCert p q cert h
    toRatFunc f = embed p / embed q ∧
      HexPolyMathlib.toPolynomial cert.num = (toRatFunc f).num ∧
      HexPolyMathlib.toPolynomial cert.den = (toRatFunc f).denom := by
  have hc := (RationalFn.check_iff p q cert).mp h
  exact ⟨toRatFunc_eq (f := RationalFn.ofCert p q cert h) hc.2.2.1 hc.1,
    num_toRatFunc (RationalFn.ofCert p q cert h), den_toRatFunc (RationalFn.ofCert p q cert h)⟩

end
end HexRationalFnMathlib
