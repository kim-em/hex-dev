/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRationalFn
public import HexPolyTheory
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.Algebra.Field.MinimalAxioms
public import Mathlib.Tactic.FieldSimp

public section

namespace HexRationalFnTheory

universe u v w
variable {K : Type u} [Field K] [DecidableEq K]
open Hex

/-- Mathlib field laws on the executable operations, powers, and casts. -/
instance field : Field (RationalFn K) :=
  { Field.ofMinimalAxioms (RationalFn K)
      RationalFn.add_assoc
      (fun f => (RationalFn.add_comm 0 f).trans (RationalFn.add_zero f))
      RationalFn.neg_add_cancel RationalFn.mul_assoc RationalFn.mul_comm
      (fun f => (RationalFn.mul_comm 1 f).trans (RationalFn.mul_one f))
      (fun _ h => RationalFn.mul_inv_cancel h) RationalFn.inv_zero
      RationalFn.left_distrib ⟨0, 1, RationalFn.zero_ne_one⟩ with
    sub := (· - ·)
    sub_eq_add_neg := fun _ _ => rfl
    div := (· / ·)
    div_eq_mul_inv := fun _ _ => rfl
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

/-- The Mathlib rational field induces the core rational field dictionary. -/
theorem ratField_eq : Field.toGrindField (K := Rat) = Lean.Grind.instFieldRat := by
  unfold Field.toGrindField Lean.Grind.instFieldRat
    CommRing.toGrindCommRing Ring.toGrindRing Semiring.toGrindSemiring
  dsimp only
  congr
  all_goals first
    | exact proof_irrel_heq _ _
    | (funext n; cases n with
      | zero => rfl
      | succ n => cases n with
        | zero => rfl
        | succ n => rfl)


/-- The Mathlib field induces the original core field dictionary. This equality
allows transport of successive extensions formed through either instance path. -/
theorem coreField_eq :
    Field.toGrindField (K := RationalFn K) = RationalFn.instField := rfl

noncomputable section

/-- Embed a dense polynomial into Mathlib's rational-function field. -/
@[expose] def embed (p : DensePoly K) : RatFunc K :=
  algebraMap (Polynomial K) (RatFunc K) (HexPolyTheory.toPolynomial p)

@[simp] theorem embed_zero : embed (0 : DensePoly K) = 0 := by simp [embed]
@[simp] theorem embed_one : embed (1 : DensePoly K) = 1 := by simp [embed]
@[simp] theorem embed_add (p q : DensePoly K) : embed (p + q) = embed p + embed q := by simp [embed]
@[simp] theorem embed_mul (p q : DensePoly K) : embed (p * q) = embed p * embed q := by simp [embed]

/-- Dense polynomial embedding into the fraction field is injective. -/
theorem embed_injective : Function.Injective (embed (K := K)) :=
  (RatFunc.algebraMap_injective K).comp HexPolyTheory.equiv.injective

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
theorem monic_den (f : RationalFn K) : (HexPolyTheory.toPolynomial f.den).Monic := by
  change (HexPolyTheory.toPolynomial f.den).leadingCoeff = 1
  rw [HexPolyTheory.leadingCoeff_toPolynomial]
  exact f.monic_den

/-- Build the executable canonical pair of a mathematical rational function. -/
def fromRatFunc (f : RatFunc K) : RationalFn K :=
  RationalFn.ofCoprime (HexPolyTheory.ofPolynomial f.num) (HexPolyTheory.ofPolynomial f.denom)
    (by
      have h := HexPolyTheory.leadingCoeff_toPolynomial (HexPolyTheory.ofPolynomial f.denom)
      rw [HexPolyTheory.toPolynomial_ofPolynomial] at h
      change (HexPolyTheory.ofPolynomial f.denom).leadingCoeff = 1
      rw [← h]
      exact f.monic_denom)
    (by
      obtain ⟨s, t, h⟩ := f.isCoprime_num_denom
      refine ⟨HexPolyTheory.ofPolynomial s, HexPolyTheory.ofPolynomial t, ?_⟩
      apply HexPolyTheory.equiv.injective
      simpa only [map_add, map_mul, map_one, HexPolyTheory.equiv_apply,
        HexPolyTheory.toPolynomial_ofPolynomial, HexPolyTheory.toPolynomial_one] using h)

/-- The mathematical inverse presentation recovers its input fraction. -/
@[simp]
theorem to_from (f : RatFunc K) : toRatFunc (fromRatFunc f) = f := by
  change algebraMap (Polynomial K) (RatFunc K)
      (HexPolyTheory.toPolynomial (HexPolyTheory.ofPolynomial f.num)) /
    algebraMap (Polynomial K) (RatFunc K)
      (HexPolyTheory.toPolynomial (HexPolyTheory.ofPolynomial f.denom)) = f
  rw [HexPolyTheory.toPolynomial_ofPolynomial, HexPolyTheory.toPolynomial_ofPolynomial,
    RatFunc.num_div_denom]

/-- Recovering canonical polynomials from the interpretation gives the stored value. -/
@[simp]
theorem from_to (f : RationalFn K) : fromRatFunc (toRatFunc f) = f :=
  toRatFunc_injective (to_from _)

/-- The stored numerator agrees with Mathlib's canonical numerator. -/
theorem num_toRatFunc (f : RationalFn K) :
    HexPolyTheory.toPolynomial f.num = (toRatFunc f).num := by
  have h := congrArg (fun g : RationalFn K => HexPolyTheory.toPolynomial g.num) (from_to f)
  change HexPolyTheory.toPolynomial (HexPolyTheory.ofPolynomial (toRatFunc f).num) =
    HexPolyTheory.toPolynomial f.num at h
  rw [HexPolyTheory.toPolynomial_ofPolynomial] at h
  exact h.symm

/-- The stored denominator agrees with Mathlib's canonical monic denominator. -/
theorem den_toRatFunc (f : RationalFn K) :
    HexPolyTheory.toPolynomial f.den = (toRatFunc f).denom := by
  have h := congrArg (fun g : RationalFn K => HexPolyTheory.toPolynomial g.den) (from_to f)
  change HexPolyTheory.toPolynomial (HexPolyTheory.ofPolynomial (toRatFunc f).denom) =
    HexPolyTheory.toPolynomial f.den at h
  rw [HexPolyTheory.toPolynomial_ofPolynomial] at h
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
  simp only [embed, HexPolyTheory.toPolynomial_C]
  exact (IsScalarTower.algebraMap_apply K (Polynomial K) (RatFunc K) a).symm

/-- The executable indeterminate maps to Mathlib's rational indeterminate. -/
@[simp]
theorem toRatFunc_X : toRatFunc (RationalFn.X : RationalFn K) = RatFunc.X := by
  rw [RationalFn.X, toRatFunc_ofPoly]
  simp [embed, HexPolyTheory.toPolynomial_monomial, Polynomial.monomial_one_one_eq_X,
    RatFunc.algebraMap_X]

/-- The executable constant embedding as a ring homomorphism. -/
@[expose] def constantHom : K →+* RationalFn K where
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
instance algebra : Algebra K (RationalFn K) := constantHom.toAlgebra

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
      (algebraMap (Polynomial K) (RatFunc K) (HexPolyTheory.toPolynomial f.num).derivative * embed f.den -
        embed f.num * algebraMap (Polynomial K) (RatFunc K) (HexPolyTheory.toPolynomial f.den).derivative) /
        (embed f.den * embed f.den) := by
  rw [toRatFunc_eq (RationalFn.derivative_spec f) (DensePoly.mul_ne_zero f.den_ne_zero f.den_ne_zero)]
  simp only [embed, HexPolyTheory.toPolynomial_sub, HexPolyTheory.toPolynomial_mul,
    HexPolyTheory.toPolynomial_derivative, map_sub, map_mul]

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
      HexPolyTheory.toPolynomial f.num = (toRatFunc f).num ∧
      HexPolyTheory.toPolynomial f.den = (toRatFunc f).denom :=
  ⟨toRatFunc_eq (RationalFn.normalize_spec p q hq) hq, num_toRatFunc _, den_toRatFunc _⟩

/-- The headline normalization theorem also holds for any lawful multiplication plan. -/
theorem normalizeWith_spec (plan : DensePoly.MulPlan K) (p q : DensePoly K) (hq : q ≠ 0) :
    let f := RationalFn.normalizeWith plan p q hq
    toRatFunc f = embed p / embed q ∧
      HexPolyTheory.toPolynomial f.num = (toRatFunc f).num ∧
      HexPolyTheory.toPolynomial f.den = (toRatFunc f).denom :=
  ⟨toRatFunc_eq (RationalFn.normalizeWith_spec plan p q hq) hq, num_toRatFunc _, den_toRatFunc _⟩

/-- Accepted certificates prove fraction and canonical-component agreement without search replay. -/
theorem check_sound (p q : DensePoly K) (cert : RationalFn.Cert K)
    (h : RationalFn.check p q cert = true) :
    let f := RationalFn.ofCert p q cert h
    toRatFunc f = embed p / embed q ∧
      HexPolyTheory.toPolynomial cert.num = (toRatFunc f).num ∧
      HexPolyTheory.toPolynomial cert.den = (toRatFunc f).denom := by
  have hc := (RationalFn.check_iff p q cert).mp h
  exact ⟨toRatFunc_eq (f := RationalFn.ofCert p q cert h) hc.2.2.1 hc.1,
    num_toRatFunc (RationalFn.ofCert p q cert h), den_toRatFunc (RationalFn.ofCert p q cert h)⟩

section Map
open scoped nonZeroDivisors
variable {L : Type v} [Field L] [DecidableEq L]

omit [DecidableEq K] [DecidableEq L] in
/-- Polynomial coefficient embeddings preserve nonzero denominators. -/
theorem map_nonzero (f : K →+* L) :
    (Polynomial K)⁰ ≤ ((Polynomial L)⁰).comap (Polynomial.mapRingHom f) := by
  intro p hp
  exact mem_nonZeroDivisors_iff_ne_zero.mpr <|
    (Polynomial.map_ne_zero_iff f.injective).mpr
      (mem_nonZeroDivisors_iff_ne_zero.mp hp)

omit [DecidableEq K] [DecidableEq L] in
/-- A field embedding reflects zero at each coefficient. -/
theorem coeff_zero_iff (f : K →+* L) (a : K) : f a = 0 ↔ a = 0 := by
  constructor
  · intro h
    exact f.injective (by simpa using h)
  · intro h
    subst a
    exact f.map_zero

private theorem toPolynomial_map (f : K →+* L) (p : DensePoly K) :
    HexPolyTheory.toPolynomial (DensePoly.Interpret.map f (coeff_zero_iff f) p) =
      (HexPolyTheory.toPolynomial p).map f := by
  ext i
  simp only [HexPolyTheory.coeff_toPolynomial, DensePoly.Interpret.map_coeff,
    Polynomial.coeff_map]

/-- Executable transport along a coefficient-field embedding. -/
@[expose] def coeffMap (f : K →+* L) (q : RationalFn K) : RationalFn L :=
  RationalFn.mapCoeffs f (coeff_zero_iff f) f.map_one (map_sub f) (map_mul f)
    (map_div₀ f) (map_inv₀ f) q

/-- Executable coefficient transport denotes the usual map of rational functions. -/
theorem toRatFunc_coeffMap (f : K →+* L) (q : RationalFn K) :
    toRatFunc (coeffMap f q) =
      RatFunc.mapRingHom (Polynomial.mapRingHom f) (map_nonzero f) (toRatFunc q) := by
  unfold coeffMap
  simp only [toRatFunc, embed, RatFunc.coe_mapRingHom_eq_coe_map]
  rw [RatFunc.map_apply_div]
  simp only [RationalFn.mapCoeffs_num, RationalFn.mapCoeffs_den,
    toPolynomial_map, Polynomial.coe_mapRingHom]

/-- Change rational-function coefficients along a field embedding. Its function
is the executable canonical-pair map. -/
@[expose] def mapHom (f : K →+* L) : RationalFn K →+* RationalFn L where
  toFun := coeffMap f
  map_zero' := by
    apply toRatFunc_injective
    rw [toRatFunc_coeffMap, toRatFunc_zero, toRatFunc_zero, map_zero]
  map_one' := by
    apply toRatFunc_injective
    rw [toRatFunc_coeffMap, toRatFunc_one, toRatFunc_one, map_one]
  map_add' p q := by
    apply toRatFunc_injective
    rw [toRatFunc_coeffMap, toRatFunc_add, toRatFunc_add,
      toRatFunc_coeffMap, toRatFunc_coeffMap, map_add]
  map_mul' p q := by
    apply toRatFunc_injective
    rw [toRatFunc_coeffMap, toRatFunc_mul, toRatFunc_mul,
      toRatFunc_coeffMap, toRatFunc_coeffMap, map_mul]

/-- The coefficient homomorphism commutes with the Mathlib fraction-field model. -/
theorem toRatFunc_mapHom (f : K →+* L) (q : RationalFn K) :
    toRatFunc (mapHom f q) =
      RatFunc.mapRingHom (Polynomial.mapRingHom f) (map_nonzero f) (toRatFunc q) :=
  toRatFunc_coeffMap f q

/-- The executable map agrees with the fraction-field coefficient homomorphism. -/
theorem coeffMap_eq_mapHom (f : K →+* L) (q : RationalFn K) :
    coeffMap f q = mapHom f q := rfl

/-- Changing coefficients along a field embedding preserves rational-function equality. -/
theorem mapHom_injective (f : K →+* L) : Function.Injective (mapHom f) := by
  intro p q h
  apply toRatFunc_injective
  apply RatFunc.map_injective (Polynomial.mapRingHom f) (map_nonzero f)
    (by simpa only [Polynomial.coe_mapRingHom] using Polynomial.map_injective f f.injective)
  simpa only [toRatFunc_mapHom, RatFunc.coe_mapRingHom_eq_coe_map] using
    congrArg toRatFunc h

/-- Executable coefficient transport is injective along a field embedding. -/
theorem coeffMap_injective (f : K →+* L) :
    Function.Injective (coeffMap f) := by
  intro p q h
  apply mapHom_injective f
  simpa only [coeffMap_eq_mapHom] using h

/-- Mapping coefficients through the identity embedding fixes each fraction. -/
theorem mapHom_id : mapHom (RingHom.id K) = RingHom.id (RationalFn K) := by
  apply RingHom.ext
  intro q
  apply RationalFn.ext
  · apply DensePoly.ext_coeff
    intro i
    change (coeffMap (RingHom.id K) q).num.coeff i = q.num.coeff i
    simp only [coeffMap, RationalFn.mapCoeffs_num,
      DensePoly.Interpret.map_coeff, RingHom.id_apply]
  · apply DensePoly.ext_coeff
    intro i
    change (coeffMap (RingHom.id K) q).den.coeff i = q.den.coeff i
    simp only [coeffMap, RationalFn.mapCoeffs_den,
      DensePoly.Interpret.map_coeff, RingHom.id_apply]

/-- Successive coefficient embeddings compose on canonical fractions. -/
theorem mapHom_comp {M : Type w} [Field M] [DecidableEq M]
    (g : L →+* M) (f : K →+* L) :
    (mapHom g).comp (mapHom f) = mapHom (g.comp f) := by
  apply RingHom.ext
  intro q
  apply RationalFn.ext
  · apply DensePoly.ext_coeff
    intro i
    change (coeffMap g (coeffMap f q)).num.coeff i =
      (coeffMap (g.comp f) q).num.coeff i
    simp only [coeffMap, RationalFn.mapCoeffs_num,
      DensePoly.Interpret.map_coeff, RingHom.comp_apply]
  · apply DensePoly.ext_coeff
    intro i
    change (coeffMap g (coeffMap f q)).den.coeff i =
      (coeffMap (g.comp f) q).den.coeff i
    simp only [coeffMap, RationalFn.mapCoeffs_den,
      DensePoly.Interpret.map_coeff, RingHom.comp_apply]

/-- Executable coefficient transport preserves addition. -/
@[simp] theorem coeffMap_add (f : K →+* L) (p q : RationalFn K) :
    coeffMap f (p + q) = coeffMap f p + coeffMap f q := by
  simp only [coeffMap_eq_mapHom, map_add]

/-- Executable coefficient transport preserves multiplication. -/
@[simp] theorem coeffMap_mul (f : K →+* L) (p q : RationalFn K) :
    coeffMap f (p * q) = coeffMap f p * coeffMap f q := by
  simp only [coeffMap_eq_mapHom, map_mul]

/-- A coefficient remains a coefficient after changing the base field. -/
@[simp] theorem mapHom_C (f : K →+* L) (a : K) :
    mapHom f (RationalFn.C a) = RationalFn.C (f a) := by
  apply toRatFunc_injective
  rw [toRatFunc_mapHom, toRatFunc_C, toRatFunc_C]
  change (RatFunc.mapRingHom (Polynomial.mapRingHom f) (map_nonzero f))
    (algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a)) =
      algebraMap (Polynomial L) (RatFunc L) (Polynomial.C (f a))
  have h := RatFunc.map_apply_div (Polynomial.mapRingHom f) (map_nonzero f)
    (Polynomial.C a) 1
  simpa only [RatFunc.coe_mapRingHom_eq_coe_map, map_one, div_one,
    Polynomial.coe_mapRingHom, Polynomial.map_C] using h

/-- Changing the coefficient field fixes the indeterminate. -/
@[simp] theorem mapHom_X (f : K →+* L) :
    mapHom f (RationalFn.X : RationalFn K) = RationalFn.X := by
  apply toRatFunc_injective
  rw [toRatFunc_mapHom, toRatFunc_X, toRatFunc_X]
  change (RatFunc.mapRingHom (Polynomial.mapRingHom f) (map_nonzero f))
    (algebraMap (Polynomial K) (RatFunc K) Polynomial.X) =
      algebraMap (Polynomial L) (RatFunc L) Polynomial.X
  have h := RatFunc.map_apply_div (Polynomial.mapRingHom f) (map_nonzero f)
    Polynomial.X 1
  simpa only [RatFunc.coe_mapRingHom_eq_coe_map, map_one, div_one,
    Polynomial.coe_mapRingHom, Polynomial.map_X] using h

/-- Executable transport maps constants through the coefficient embedding. -/
@[simp] theorem coeffMap_C (f : K →+* L) (a : K) :
    coeffMap f (RationalFn.C a) =
      RationalFn.C (f a) := by
  rw [coeffMap_eq_mapHom, mapHom_C]

/-- Executable transport fixes the indeterminate. -/
@[simp] theorem coeffMap_X (f : K →+* L) :
    coeffMap f (RationalFn.X : RationalFn K) =
      RationalFn.X := by
  rw [coeffMap_eq_mapHom, mapHom_X]

end Map

end
end HexRationalFnTheory
