/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRationalFn.Basic
public import HexPolyFast.HalfGcd
public import HexPolyFast.Karatsuba

public section

namespace Hex.RationalFn

universe u
variable {K : Type u} [Lean.Grind.Field K] [DecidableEq K]
open DensePoly

omit [DecidableEq K] in
/-- The inverse of a nonzero coefficient is nonzero. -/
theorem inv_ne_zero {a : K} (ha : a ≠ 0) : a⁻¹ ≠ 0 := by
  have h := Lean.Grind.Field.inv_mul_cancel ha
  intro hz
  rw [hz, Lean.Grind.Semiring.zero_mul] at h
  exact Lean.Grind.Field.zero_ne_one h

/-- Schoolbook base-case length for the default Karatsuba plan. -/
def defaultCutoff : Nat := 8

/-- The generic multiplication plan used by rational-function arithmetic. -/
def defaultPlan : MulPlan K := karatsubaPlan defaultCutoff

/-- Exact division with a lawful multiplication plan and a divisibility witness. -/
@[expose]
def exactWith (plan : MulPlan K) (p q : DensePoly K) (_h : q ∣ p) : DensePoly K :=
  (divModWith plan p q).1

/-- Exact division reconstructs its dividend. -/
theorem exact_spec (plan : MulPlan K) (p q : DensePoly K) (h : q ∣ p) :
    p = q * exactWith plan p q h := by
  have hr := divMod_spec p q
  have hz := mod_eq_zero_of_dvd p q h
  change (divMod p q).2 = 0 at hz
  simp only [exactWith, divModWith_eq]
  grind

/-- The remainder discarded by exact division is zero. -/
theorem exact_remainder (plan : MulPlan K) (p q : DensePoly K) (h : q ∣ p) :
    (divModWith plan p q).2 = 0 := by
  rw [divModWith_eq]
  exact mod_eq_zero_of_dvd p q h

/-- An exact quotient of a nonzero dividend is nonzero. -/
theorem exact_ne_zero (plan : MulPlan K) (p q : DensePoly K)
    (h : q ∣ p) (hp : p ≠ 0) : exactWith plan p q h ≠ 0 := by
  have he := exact_spec plan p q h
  intro hz
  apply hp
  grind

/-- The monic gcd computed using a supplied plan. -/
@[expose]
def commonWith (plan : MulPlan K) (p q : DensePoly K) : DensePoly K :=
  monicize (gcdWith plan p q)

/-- The common factor has plan-independent semantics. -/
theorem common_eq (plan : MulPlan K) (p q : DensePoly K) :
    commonWith plan p q = monicize (gcd p q) := by
  rw [commonWith, gcdWith_eq]

/-- A common factor with a nonzero right input is nonzero and divides both inputs. -/
theorem common_spec (plan : MulPlan K) (p q : DensePoly K) (hq : q ≠ 0) :
    commonWith plan p q ≠ 0 ∧ commonWith plan p q ∣ p ∧ commonWith plan p q ∣ q := by
  rw [common_eq]
  have hg := gcd_ne_zero_right p q hq
  exact ⟨monicize_ne_zero hg, monicize_dvd_of_dvd hg (gcd_dvd_left p q),
    monicize_dvd_of_dvd hg (gcd_dvd_right p q)⟩

/-- Normalize a fraction by cancelling its gcd and making its denominator monic. -/
@[expose]
def normalizeWith (plan : MulPlan K) (p q : DensePoly K) (hq : q ≠ 0) : RationalFn K :=
  if p = 0 then 0 else
    let d := commonWith plan p q
    have hd := common_spec plan p q hq
    let a := exactWith plan p d hd.2.1
    let b := exactWith plan q d hd.2.2
    have hb : b ≠ 0 := exact_ne_zero plan q d hd.2.2 hq
    have hab : Coprime a b := coprime_cofactors hd.1
      (exact_spec plan p d hd.2.1) (exact_spec plan q d hd.2.2)
      (by rw [common_eq]; exact bezout_monicize_gcd p q)
    ⟨scale b.leadingCoeff⁻¹ a, scale b.leadingCoeff⁻¹ b,
      by rw [scale_inv_eq_monicize hb]; exact monicize_monic hb,
      (coprime_iff _ _).mp
        (((hab.scale_left (inv_ne_zero (leadingCoeff_ne_zero hb))).symm.scale_left
          (inv_ne_zero (leadingCoeff_ne_zero hb))).symm)⟩

/-- Normalize with the default multiplication plan. -/
@[expose]
def normalize (p q : DensePoly K) (hq : q ≠ 0) : RationalFn K :=
  normalizeWith defaultPlan p q hq

/-- A normalized pair represents the input fraction. -/
theorem normalizeWith_spec (plan : MulPlan K) (p q : DensePoly K) (hq : q ≠ 0) :
    (normalizeWith plan p q hq).num * q = p * (normalizeWith plan p q hq).den := by
  unfold normalizeWith
  split
  · rename_i hp
    change 0 * q = p * 1
    grind
  · dsimp only
    have hd := common_spec plan p q hq
    have hp := exact_spec plan p (commonWith plan p q) hd.2.1
    have hq' := exact_spec plan q (commonWith plan p q) hd.2.2
    rw [scale_eq_C_mul, scale_eq_C_mul]
    grind

/-- Default normalization preserves the represented fraction. -/
theorem normalize_spec (p q : DensePoly K) (hq : q ≠ 0) :
    (normalize p q hq).num * q = p * (normalize p q hq).den :=
  normalizeWith_spec defaultPlan p q hq

/-- A canonical representative of the input fraction equals its normalization. -/
theorem normalize_unique (plan : MulPlan K) (p q : DensePoly K) (hq : q ≠ 0)
    (f : RationalFn K) (h : f.num * q = p * f.den) :
    f = normalizeWith plan p q hq := by
  apply (eq_iff _ _).mpr
  have hn := normalizeWith_spec plan p q hq
  apply mul_right_cancel hq
  grind

/-- Normalization is independent of the supplied lawful plan. -/
theorem normalizeWith_eq (plan : MulPlan K) (p q : DensePoly K) (hq : q ≠ 0) :
    normalizeWith plan p q hq = normalize p q hq :=
  normalize_unique defaultPlan p q hq _ (normalizeWith_spec plan p q hq)

/-- Normalizing a stored pair returns that same value. -/
theorem normalize_self (f : RationalFn K) : normalize f.num f.den f.den_ne_zero = f :=
  (normalize_unique defaultPlan f.num f.den f.den_ne_zero f rfl).symm

/-- Checked fraction construction rejects a zero denominator, including zero over zero. -/
@[expose]
def ofFraction? (p q : DensePoly K) : Option (RationalFn K) :=
  if hq : q = 0 then none else some (normalize p q hq)

/-- Checked construction fails precisely for zero denominators. -/
theorem ofFraction?_eq_none (p q : DensePoly K) : ofFraction? p q = none ↔ q = 0 := by
  unfold ofFraction?
  split <;> simp_all

/-- Multiplying a presentation by a common nonzero factor changes no value. -/
theorem normalize_mul (p q r : DensePoly K) (hq : q ≠ 0) (hr : r ≠ 0) :
    normalize (p * r) (q * r) (mul_ne_zero hq hr) = normalize p q hq := by
  apply (normalize_unique defaultPlan (p * r) (q * r) (mul_ne_zero hq hr)
    (normalize p q hq) ?_).symm
  have h := normalize_spec p q hq
  grind

/-- A valid checked fraction is the default normalization. -/
theorem ofFraction?_eq_some (p q : DensePoly K) (hq : q ≠ 0) :
    ofFraction? p q = some (normalize p q hq) := by
  simp [ofFraction?, hq]

/-- Coprime cofactors and the common monic factor removed from two polynomials. -/
structure Cofactors (p q : DensePoly K) where
  /-- Monic common factor. -/
  common : DensePoly K
  /-- Left input divided by the common factor. -/
  left : DensePoly K
  /-- Right input divided by the common factor. -/
  right : DensePoly K
  /-- Monicity of the common factor. -/
  monic : common.Monic
  /-- Reconstruction of the left input. -/
  left_spec : p = common * left
  /-- Reconstruction of the right input. -/
  right_spec : q = common * right
  /-- The remaining factors are coprime. -/
  coprime : Coprime left right

/-- Compute coprime cofactors using fast gcd and two exact divisions. -/
@[expose]
def cancelWith (plan : MulPlan K) (p q : DensePoly K) (hq : q ≠ 0) : Cofactors p q :=
  let d := commonWith plan p q
  have hd := common_spec plan p q hq
  ⟨d, exactWith plan p d hd.2.1, exactWith plan q d hd.2.2,
    by change (commonWith plan p q).Monic
       rw [common_eq]
       exact monicize_monic (gcd_ne_zero_right p q hq),
    exact_spec plan p d hd.2.1, exact_spec plan q d hd.2.2,
    coprime_cofactors hd.1 (exact_spec plan p d hd.2.1)
      (exact_spec plan q d hd.2.2)
      (by rw [common_eq]; exact bezout_monicize_gcd p q)⟩

/-- A left cofactor divides its input. -/
theorem Cofactors.left_dvd {p q : DensePoly K} (r : Cofactors p q) : r.left ∣ p :=
  ⟨r.common, by have h := r.left_spec; grind⟩

/-- A right cofactor divides its input. -/
theorem Cofactors.right_dvd {p q : DensePoly K} (r : Cofactors p q) : r.right ∣ q :=
  ⟨r.common, by have h := r.right_spec; grind⟩

/-- Removing a monic factor preserves monicity on the left. -/
theorem Cofactors.monic_left {p q : DensePoly K} (r : Cofactors p q) (hp : p.Monic) :
    r.left.Monic := monic_of_mul r.monic (r.left_spec ▸ hp)

/-- Removing a monic factor preserves monicity on the right. -/
theorem Cofactors.monic_right {p q : DensePoly K} (r : Cofactors p q) (hq : q.Monic) :
    r.right.Monic := monic_of_mul r.monic (r.right_spec ▸ hq)

end Hex.RationalFn
