/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRationalFn.Arithmetic

public section

namespace Hex.RationalFn

universe u
variable {K : Type u} [Lean.Grind.Field K] [DecidableEq K]
open DensePoly

/-- A cross-product identity relating a canonical value to a fraction presentation. -/
@[expose]
def Represents (f : RationalFn K) (p q : DensePoly K) : Prop := f.num * q = p * f.den

/-- Every value represents its stored fraction. -/
theorem represents_self (f : RationalFn K) : Represents f f.num f.den := rfl

/-- Equal fraction presentations with nonzero denominator identify canonical values. -/
theorem Represents.eq {f g : RationalFn K} {p q : DensePoly K}
    (hf : Represents f p q) (hg : Represents g p q) (hq : q ≠ 0) : f = g := by
  apply (eq_iff _ _).mpr
  apply DensePoly.mul_right_cancel hq
  unfold Represents at hf hg
  grind

/-- Addition respects arbitrary fraction presentations. -/
theorem Represents.add {f g : RationalFn K} {a b c d : DensePoly K}
    (hf : Represents f a b) (hg : Represents g c d) :
    Represents (f + g) (a * d + c * b) (b * d) := by
  unfold Represents at *
  apply DensePoly.mul_right_cancel (mul_ne_zero f.den_ne_zero g.den_ne_zero)
  have hs := add_spec f g
  grind

/-- Multiplication respects arbitrary fraction presentations. -/
theorem Represents.mul {f g : RationalFn K} {a b c d : DensePoly K}
    (hf : Represents f a b) (hg : Represents g c d) :
    Represents (f * g) (a * c) (b * d) := by
  unfold Represents at *
  apply DensePoly.mul_right_cancel (mul_ne_zero f.den_ne_zero g.den_ne_zero)
  have hs := mul_spec f g
  grind

/-- Negation respects fraction presentations. -/
theorem Represents.neg {f : RationalFn K} {a b : DensePoly K}
    (hf : Represents f a b) : Represents (-f) (-a) b := by
  change (-f.num) * b = (-a) * f.den
  unfold Represents at hf
  grind

/-- A polynomial represents itself over one. -/
theorem represents_ofPoly (p : DensePoly K) : Represents (ofPoly p) p 1 := rfl

/-- Zero is an additive identity. -/
theorem add_zero (f : RationalFn K) : f + 0 = f := by
  apply (eq_iff _ _).mpr
  have h := add_spec f 0
  change (f + 0).num * (f.den * 1) = (f.num * 1 + 0 * f.den) * (f + 0).den at h
  grind

/-- Addition is commutative. -/
theorem add_comm (f g : RationalFn K) : f + g = g + f := by
  have h := (represents_self f).add (represents_self g)
  apply h.eq _ (mul_ne_zero f.den_ne_zero g.den_ne_zero)
  have h' := (represents_self g).add (represents_self f)
  unfold Represents at *
  grind

/-- Addition is associative. -/
theorem add_assoc (f g h : RationalFn K) : f + g + h = f + (g + h) := by
  have hl := ((represents_self f).add (represents_self g)).add (represents_self h)
  apply hl.eq _ (mul_ne_zero (mul_ne_zero f.den_ne_zero g.den_ne_zero) h.den_ne_zero)
  have hr := (represents_self f).add ((represents_self g).add (represents_self h))
  unfold Represents at *
  grind

/-- Multiplication is commutative. -/
theorem mul_comm (f g : RationalFn K) : f * g = g * f := by
  have h := (represents_self f).mul (represents_self g)
  apply h.eq _ (mul_ne_zero f.den_ne_zero g.den_ne_zero)
  have h' := (represents_self g).mul (represents_self f)
  unfold Represents at *
  grind

/-- Multiplication is associative. -/
theorem mul_assoc (f g h : RationalFn K) : f * g * h = f * (g * h) := by
  have hl := ((represents_self f).mul (represents_self g)).mul (represents_self h)
  apply hl.eq _ (mul_ne_zero (mul_ne_zero f.den_ne_zero g.den_ne_zero) h.den_ne_zero)
  have hr := (represents_self f).mul ((represents_self g).mul (represents_self h))
  unfold Represents at *
  grind

/-- One is a multiplicative identity. -/
theorem mul_one (f : RationalFn K) : f * 1 = f := by
  apply (eq_iff _ _).mpr
  have h := mul_spec f 1
  change (f * 1).num * (f.den * 1) = (f.num * 1) * (f * 1).den at h
  grind

/-- Zero absorbs multiplication. -/
theorem zero_mul (f : RationalFn K) : 0 * f = 0 := by
  apply (num_eq_zero _).mp
  have h := mul_spec 0 f
  change (0 * f).num * (1 * f.den) = (0 * f.num) * (0 * f).den at h
  apply DensePoly.mul_right_cancel f.den_ne_zero
  grind

/-- Multiplication distributes over addition. -/
theorem left_distrib (f g h : RationalFn K) : f * (g + h) = f * g + f * h := by
  have hl := (represents_self f).mul ((represents_self g).add (represents_self h))
  have hr := ((represents_self f).mul (represents_self g)).add
    ((represents_self f).mul (represents_self h))
  apply (eq_iff _ _).mpr
  apply DensePoly.mul_right_cancel
    (mul_ne_zero f.den_ne_zero (mul_ne_zero f.den_ne_zero (mul_ne_zero g.den_ne_zero h.den_ne_zero)))
  unfold Represents at hl hr
  grind

/-- Negation supplies additive inverses. -/
theorem neg_add_cancel (f : RationalFn K) : -f + f = 0 := by
  have h := (represents_self f).neg.add (represents_self f)
  apply h.eq _ (mul_ne_zero f.den_ne_zero f.den_ne_zero)
  change 0 * (f.den * f.den) = (-f.num * f.den + f.num * f.den) * 1
  grind

/-- Polynomial embedding preserves addition. -/
theorem ofPoly_add (p q : DensePoly K) : ofPoly (p + q) = ofPoly p + ofPoly q := by
  symm
  have h := (represents_ofPoly p).add (represents_ofPoly q)
  apply h.eq _ (mul_ne_zero (monic_ne_zero monic_one) (monic_ne_zero monic_one))
  change (p + q) * (1 * 1) = (p * 1 + q * 1) * 1
  grind

/-- Polynomial embedding preserves multiplication. -/
theorem ofPoly_mul (p q : DensePoly K) : ofPoly (p * q) = ofPoly p * ofPoly q := by
  symm
  have h := (represents_ofPoly p).mul (represents_ofPoly q)
  apply h.eq _ (mul_ne_zero (monic_ne_zero monic_one) (monic_ne_zero monic_one))
  change (p * q) * (1 * 1) = (p * q) * 1
  grind

/-- Polynomial embedding preserves negation. -/
theorem ofPoly_neg (p : DensePoly K) : ofPoly (-p) = -(ofPoly p) := rfl

/-- The zeroth natural power is one, including for zero. -/
theorem pow_zero (f : RationalFn K) : f ^ (0 : Nat) = 1 := by
  apply ext
  · rw [num_pow, Lean.Grind.Semiring.pow_zero]; rfl
  · rw [den_pow, Lean.Grind.Semiring.pow_zero]; rfl

/-- Binary powering satisfies the successor law. -/
theorem pow_succ (f : RationalFn K) (n : Nat) : f ^ (n + 1) = f ^ n * f := by
  apply (eq_iff _ _).mpr
  have h := mul_spec (f ^ n) f
  rw [num_pow, den_pow] at h
  rw [num_pow, den_pow, Lean.Grind.Semiring.pow_succ, Lean.Grind.Semiring.pow_succ]
  exact h.symm

attribute [local instance] Lean.Grind.Semiring.natCast Lean.Grind.Ring.intCast

instance : NatCast (RationalFn K) := ⟨fun n => ofPoly (Nat.cast n)⟩
instance (n : Nat) : OfNat (RationalFn K) n := ⟨ofPoly (OfNat.ofNat n)⟩
instance : IntCast (RationalFn K) := ⟨fun n => ofPoly (Int.cast n)⟩
instance : SMul Nat (RationalFn K) := ⟨fun n f => (Nat.cast n : RationalFn K) * f⟩
instance : SMul Int (RationalFn K) := ⟨fun n f => (Int.cast n : RationalFn K) * f⟩

/-- The executable arithmetic forms a commutative ring without Mathlib. -/
instance instCommRing : Lean.Grind.CommRing (RationalFn K) where
  add_zero := add_zero
  add_comm := add_comm
  add_assoc := add_assoc
  mul_assoc := mul_assoc
  mul_comm := mul_comm
  mul_one := mul_one
  one_mul f := (mul_comm 1 f).trans (mul_one f)
  left_distrib := left_distrib
  right_distrib f g h := by rw [mul_comm, left_distrib, mul_comm h f, mul_comm h g]
  zero_mul := zero_mul
  mul_zero f := (mul_comm f 0).trans (zero_mul f)
  pow_zero := pow_zero
  pow_succ := pow_succ
  ofNat_succ n := by
    change ofPoly (OfNat.ofNat (n + 1)) = ofPoly (OfNat.ofNat n) + ofPoly 1
    rw [← ofPoly_add, Lean.Grind.Semiring.ofNat_succ]
  ofNat_eq_natCast n := by
    change ofPoly (OfNat.ofNat n) = ofPoly (Nat.cast n)
    rw [Lean.Grind.Semiring.ofNat_eq_natCast]
  neg_add_cancel := neg_add_cancel
  sub_eq_add_neg _ _ := rfl
  neg_zsmul i f := by
    change ofPoly (Int.cast (-i)) * f = -(ofPoly (Int.cast i) * f)
    rw [Lean.Grind.Ring.intCast_neg, ofPoly_neg]
    have h := (represents_ofPoly (Int.cast i)).neg.mul (represents_self f)
    apply h.eq _ (mul_ne_zero (monic_ne_zero monic_one) f.den_ne_zero)
    have h' := ((represents_ofPoly (Int.cast i)).mul (represents_self f)).neg
    unfold Represents at *
    grind
  zsmul_natCast_eq_nsmul n f := by
    change ofPoly (Int.cast (n : Int)) * f = ofPoly (Nat.cast n) * f
    rw [Lean.Grind.Ring.intCast_natCast]
  intCast_ofNat n := by
    change ofPoly (Int.cast (n : Int)) = ofPoly (OfNat.ofNat n)
    rw [Lean.Grind.Ring.intCast_natCast, Lean.Grind.Semiring.ofNat_eq_natCast]
  intCast_neg i := by
    change ofPoly (Int.cast (-i)) = -(ofPoly (Int.cast i))
    rw [Lean.Grind.Ring.intCast_neg, ofPoly_neg]

/-- A nonzero rational function multiplied by its inverse is one. -/
theorem mul_inv_cancel {f : RationalFn K} (hf : f ≠ 0) : f * f⁻¹ = 1 := by
  have hn : f.num ≠ 0 := fun h => hf ((num_eq_zero f).mp h)
  have hi := inv_spec f hn
  have hm := mul_spec f f⁻¹
  apply (eq_iff _ _).mpr
  change (f * f⁻¹).num * 1 = 1 * (f * f⁻¹).den
  apply DensePoly.mul_right_cancel (mul_ne_zero f.den_ne_zero f⁻¹.den_ne_zero)
  grind

/-- Zero and one are distinct canonical pairs. -/
theorem zero_ne_one : (0 : RationalFn K) ≠ 1 := by
  intro h
  have hn := congrArg num h
  exact monic_ne_zero (monic_one (K := K)) hn.symm

/-- Applying total inversion twice restores the original value. -/
theorem inv_inv (f : RationalFn K) : f⁻¹⁻¹ = f := by
  by_cases hf : f = 0
  · rw [hf, inv_zero, inv_zero]
  · have h := mul_inv_cancel hf
    have hi : f⁻¹ ≠ 0 := by intro hi; rw [hi] at h; grind [zero_ne_one (K := K)]
    have h' := mul_inv_cancel hi
    grind

instance : HPow (RationalFn K) Int (RationalFn K) :=
  ⟨fun f n => match n with
    | .ofNat n => f ^ n
    | .negSucc n => (f ^ (n + 1))⁻¹⟩

/-- Rational functions form a lawful effective field with total division. -/
instance instField : Lean.Grind.Field (RationalFn K) where
  div_eq_mul_inv _ _ := rfl
  zero_ne_one := zero_ne_one
  inv_zero := inv_zero
  mul_inv_cancel := mul_inv_cancel
  zpow_zero := pow_zero
  zpow_succ := pow_succ
  zpow_neg f n := by
    cases n with
    | ofNat n =>
      cases n with
      | zero =>
        change f ^ (0 : Nat) = (f ^ (0 : Nat))⁻¹
        rw [pow_zero]
        have h := mul_inv_cancel (fun h => zero_ne_one h.symm : (1 : RationalFn K) ≠ 0)
        grind
      | succ n => rfl
    | negSucc n => exact (inv_inv (f ^ (n + 1))).symm

/-- Constants preserve zero. -/
theorem C_zero : C (0 : K) = 0 := by
  apply ext
  · change DensePoly.C (0 : K) = (0 : DensePoly K)
    apply DensePoly.ext_coeff; intro n
    simp only [coeff_C, coeff_zero]
    split <;> rfl
  · rfl

/-- Constants preserve one. -/
theorem C_one : C (1 : K) = 1 := rfl

/-- Constants preserve addition. -/
theorem C_add (a b : K) : C (a + b) = C a + C b := by
  change ofPoly (DensePoly.C (a + b)) = ofPoly (DensePoly.C a) + ofPoly (DensePoly.C b)
  rw [← ofPoly_add]
  congr 1
  apply DensePoly.ext_coeff; intro n
  simp only [coeff_add_semiring, coeff_C]
  split
  · rfl
  · change (0 : K) = 0 + 0
    grind

/-- Constants preserve multiplication. -/
theorem C_mul (a b : K) : C (a * b) = C a * C b := by
  change ofPoly (DensePoly.C (a * b)) = ofPoly (DensePoly.C a) * ofPoly (DensePoly.C b)
  rw [← ofPoly_mul, DensePoly.C_mul_C]

/-- Constants preserve total inversion. -/
theorem C_inv (a : K) : C a⁻¹ = (C a)⁻¹ := by
  by_cases ha : a = 0
  · subst a
    rw [Lean.Grind.Field.inv_zero, C_zero, inv_zero]
  · have hc : C a ≠ 0 := by
      intro h
      have hn := congrArg (fun f : RationalFn K => f.num.coeff 0) h
      change (DensePoly.C a).coeff 0 = (0 : DensePoly K).coeff 0 at hn
      apply ha
      simpa using hn
    have h : C a * C a⁻¹ = 1 := by
      rw [← C_mul, Lean.Grind.Field.mul_inv_cancel ha, C_one]
    have h' := mul_inv_cancel hc
    grind

end Hex.RationalFn
