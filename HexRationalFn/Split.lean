/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRationalFn.Eval

public section

namespace Hex.RationalFn

universe u
variable {K : Type u} [Lean.Grind.Field K] [DecidableEq K]
open DensePoly

/-- A proper rational function has numerator degree below denominator degree. -/
@[expose]
def Proper (f : RationalFn K) : Prop := f.num = 0 ∨ f.num.size < f.den.size

/-- Stored sizes express properness uniformly, including zero. -/
theorem proper_iff (f : RationalFn K) : Proper f ↔ f.num.size < f.den.size := by
  have hd : 0 < f.den.size := Nat.pos_of_ne_zero
    (fun h => f.den_ne_zero ((size_eq_zero_iff f.den).mp h))
  unfold Proper
  constructor
  · rintro (h | h)
    · rw [h, size_zero]; exact hd
    · exact h
  · exact Or.inr

/-- Fast polynomial division leaves a remainder smaller than its nonzero divisor. -/
theorem remainder_bound (plan : MulPlan K) (p q : DensePoly K) (hq : q ≠ 0) :
    (divModWith plan p q).2.size < q.size := divModWith_size_lt plan p q hq

/-- A division remainder retains coprimality with the denominator. -/
theorem remainder_coprime (plan : MulPlan K) (f : RationalFn K) :
    Coprime (divModWith plan f.num f.den).2 f.den := by
  have hr := divMod_spec f.num f.den
  rw [divModWith_eq]
  have h := f.bezout.add_mul (r := -(divMod f.num f.den).1)
  have he : f.num + -(divMod f.num f.den).1 * f.den = (divMod f.num f.den).2 := by grind
  rw [he] at h
  exact h

/-- Separate the polynomial part with one division and no additional gcd. -/
@[expose]
def splitWith (plan : MulPlan K) (f : RationalFn K) : DensePoly K × RationalFn K :=
  let qr := divModWith plan f.num f.den
  (qr.1, ofCoprime qr.2 f.den f.monic_den (remainder_coprime plan f))

/-- Polynomial-part decomposition with the default multiplication plan. -/
@[expose]
def split (f : RationalFn K) : DensePoly K × RationalFn K := splitWith defaultPlan f

/-- Splitting reconstructs its input and leaves a proper rational function. -/
theorem splitWith_spec (plan : MulPlan K) (f : RationalFn K) :
    f = ofPoly (splitWith plan f).1 + (splitWith plan f).2 ∧ Proper (splitWith plan f).2 := by
  constructor
  · apply (eq_iff _ _).mpr
    have h := (represents_ofPoly (splitWith plan f).1).add (represents_self (splitWith plan f).2)
    have hr := divMod_spec f.num f.den
    change f.num * (ofPoly (splitWith plan f).1 + (splitWith plan f).2).den =
      (ofPoly (splitWith plan f).1 + (splitWith plan f).2).num * f.den
    change (ofPoly (splitWith plan f).1 + (splitWith plan f).2).num * (1 * f.den) =
      ((divModWith plan f.num f.den).1 * f.den + (divModWith plan f.num f.den).2 * 1) *
        (ofPoly (splitWith plan f).1 + (splitWith plan f).2).den at h
    rw [divModWith_eq] at h
    grind
  · exact Or.inr (remainder_bound plan f.num f.den f.den_ne_zero)

/-- Default splitting reconstructs its input and leaves a proper rational function. -/
theorem split_spec (f : RationalFn K) : f = ofPoly (split f).1 + (split f).2 ∧ Proper (split f).2 :=
  splitWith_spec defaultPlan f

/-- Adding a polynomial leaves the canonical denominator unchanged. -/
theorem den_add_ofPoly (p : DensePoly K) (f : RationalFn K) : (ofPoly p + f).den = f.den := by
  apply monic_dvd_antisymm (ofPoly p + f).monic_den f.monic_den
  · have h := ((represents_ofPoly p).add (represents_self f)).den_dvd
    simpa only [Lean.Grind.Semiring.one_mul] using h
  · have h := ((represents_ofPoly p).neg.add (represents_self (ofPoly p + f))).den_dvd
    have he : -ofPoly p + (ofPoly p + f) = f := by grind
    rw [he] at h
    simpa only [Lean.Grind.Semiring.one_mul] using h

private theorem quotient_unique {a b q r q' r' : DensePoly K} (hb : b ≠ 0)
    (h : a = q * b + r) (h' : a = q' * b + r')
    (hr : r.size < b.size) (hr' : r'.size < b.size) : q = q' := by
  by_cases hne : q = q'
  · exact hne
  apply False.elim
  have hd : q - q' ≠ 0 := by intro h; apply hne; grind
  have hm : (q - q') * b = r' - r := by grind
  have hs := size_mul_field (q - q') b hd hb
  have hdiff : 0 < (q - q').size := Nat.pos_of_ne_zero (fun h => hd ((size_eq_zero_iff _).mp h))
  have hsub := size_sub_le_max r' r
  rw [hm] at hs
  omega

/-- The polynomial plus proper-fraction decomposition is unique. -/
theorem split_unique (f : RationalFn K) (p : DensePoly K) (s : RationalFn K)
    (h : f = ofPoly p + s) (hs : Proper s) : split f = (p, s) := by
  have hd : f.den = s.den := by rw [h, den_add_ofPoly]
  have hrep := (represents_ofPoly p).add (represents_self s)
  rw [← h] at hrep
  have hrec : f.num = p * f.den + s.num := by
    apply DensePoly.mul_right_cancel f.den_ne_zero
    unfold Represents at hrep
    rw [← hd] at hrep
    grind
  have hr := divMod_spec f.num f.den
  have hp : (split f).1 = p := by
    apply quotient_unique f.den_ne_zero
      (a := f.num) (r := (divModWith defaultPlan f.num f.den).2) (r' := s.num)
    · change f.num = (divModWith defaultPlan f.num f.den).1 * f.den +
        (divModWith defaultPlan f.num f.den).2
      rw [divModWith_eq]
      exact hr.symm
    · exact hrec
    · exact remainder_bound defaultPlan f.num f.den f.den_ne_zero
    · rw [hd]; exact (proper_iff s).mp hs
  have he : (split f).2 = s := by
    have h' := (split_spec f).1
    rw [hp] at h'
    grind
  exact Prod.ext hp he

/-- Polynomial-part splitting is independent of the lawful plan. -/
theorem splitWith_eq (plan : MulPlan K) (f : RationalFn K) : splitWith plan f = split f :=
  (split_unique f _ _ (splitWith_spec plan f).1 (splitWith_spec plan f).2).symm

/-- Recognize polynomial values by the canonical denominator being one. -/
@[expose]
def toPoly? (f : RationalFn K) : Option (DensePoly K) := if f.den = 1 then some f.num else none

/-- Polynomial recognition succeeds precisely on the polynomial embedding. -/
theorem toPoly?_eq_some (f : RationalFn K) (p : DensePoly K) :
    toPoly? f = some p ↔ f = ofPoly p := by
  unfold toPoly?
  split
  · rename_i hd
    simp only [Option.some.injEq]
    constructor
    · intro hn; exact ext hn hd
    · intro h; exact congrArg num h
  · rename_i hd
    constructor
    · intro h; cases h
    · intro h; exact False.elim (hd (congrArg den h))

end Hex.RationalFn
