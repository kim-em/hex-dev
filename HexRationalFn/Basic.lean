/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPoly

public section

namespace Hex

universe u

/-- A univariate rational function stored as coprime polynomials with monic denominator. -/
structure RationalFn (K : Type u) [Lean.Grind.Field K] [DecidableEq K] where
  /-- Canonical numerator. -/
  num : DensePoly K
  /-- Canonical denominator. -/
  den : DensePoly K
  /-- The denominator has leading coefficient one. -/
  monic_den : den.Monic
  /-- The numerator and denominator have no nonunit common factor. -/
  coprime : DensePoly.monicize (DensePoly.gcd num den) = 1

namespace RationalFn

variable {K : Type u} [Lean.Grind.Field K] [DecidableEq K]

/-- Stored polynomials determine a rational function. -/
@[ext]
theorem ext {f g : RationalFn K} (hn : f.num = g.num) (hd : f.den = g.den) : f = g := by
  cases f
  cases g
  cases hn
  cases hd
  rfl

instance : DecidableEq (RationalFn K) := fun f g =>
  if hn : f.num = g.num then
    if hd : f.den = g.den then isTrue (ext hn hd)
    else isFalse (fun h => hd (congrArg den h))
  else isFalse (fun h => hn (congrArg num h))

/-- Equality compares canonical coefficient arrays without polynomial products. -/
instance : BEq (RationalFn K) := ⟨fun f g => decide (f = g)⟩

instance : LawfulBEq (RationalFn K) where
  eq_of_beq := by simp [BEq.beq]
  rfl := by simp [BEq.beq]

/-- The stored denominator is nonzero. -/
theorem den_ne_zero (f : RationalFn K) : f.den ≠ 0 :=
  DensePoly.monic_ne_zero f.monic_den

/-- The stored pair admits a Bézout identity. -/
theorem bezout (f : RationalFn K) : DensePoly.Coprime f.num f.den :=
  (DensePoly.coprime_iff _ _).mpr f.coprime

/-- Embed a polynomial with denominator one. -/
@[expose]
def ofPoly (p : DensePoly K) : RationalFn K :=
  ⟨p, 1, DensePoly.monic_one, (DensePoly.coprime_iff _ _).mp (.one_right p)⟩

instance : Zero (RationalFn K) := ⟨ofPoly 0⟩
instance : One (RationalFn K) := ⟨ofPoly 1⟩

/-- Polynomial embedding preserves zero. -/
theorem ofPoly_zero : ofPoly (0 : DensePoly K) = 0 := rfl

/-- Polynomial embedding preserves one. -/
theorem ofPoly_one : ofPoly (1 : DensePoly K) = 1 := rfl

/-- Embed a coefficient as a constant rational function. -/
@[expose]
def C (a : K) : RationalFn K := ofPoly (DensePoly.C a)

/-- The polynomial indeterminate as a rational function. -/
@[expose]
def X : RationalFn K := ofPoly (DensePoly.monomial 1 1)

/-- Canonical pairs are equal precisely when their cross products agree. -/
theorem eq_iff (f g : RationalFn K) :
    f = g ↔ f.num * g.den = g.num * f.den := by
  constructor
  · intro h
    subst g
    rfl
  · intro h
    have hd : f.den = g.den := by
      apply DensePoly.monic_dvd_antisymm f.monic_den g.monic_den
      · apply f.bezout.dvd_of_dvd_mul
        exact ⟨g.num, by grind⟩
      · apply g.bezout.dvd_of_dvd_mul
        exact ⟨f.num, by grind⟩
    apply ext _ hd
    apply DensePoly.mul_right_cancel f.den_ne_zero
    rw [← hd] at h
    exact h

/-- Polynomial embedding is injective. -/
theorem ofPoly_injective {p q : DensePoly K} (h : ofPoly p = ofPoly q) : p = q :=
  congrArg num h

/-- A rational function is zero exactly when its numerator is zero. -/
theorem num_eq_zero (f : RationalFn K) : f.num = 0 ↔ f = 0 := by
  rw [eq_iff]
  change f.num = 0 ↔ f.num * 1 = 0 * f.den
  grind

/-- Zero has denominator one, including for a pair supplied directly with proofs. -/
theorem den_eq_one {f : RationalFn K} (h : f.num = 0) : f.den = 1 := by
  rw [(num_eq_zero f).mp h]
  rfl

end RationalFn
end Hex
