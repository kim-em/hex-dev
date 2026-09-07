/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRationalFn.Normalize

public section

namespace Hex.RationalFn

universe u
variable {K : Type u} [Lean.Grind.Field K] [DecidableEq K]
open DensePoly

/-- Construct directly from a monic denominator and a Bézout proof. -/
@[expose]
def ofCoprime (p q : DensePoly K) (hq : q.Monic) (h : Coprime p q) : RationalFn K :=
  ⟨p, q, hq, (coprime_iff _ _).mp h⟩

/-- Negation changes only the numerator. -/
@[expose]
def neg (f : RationalFn K) : RationalFn K :=
  ofCoprime (-f.num) f.den f.monic_den (by
    rcases f.bezout with ⟨s, t, h⟩
    exact ⟨-s, t, by grind⟩)

instance : Neg (RationalFn K) := ⟨neg⟩

/-- The numerator of a sum is coprime to the denominator cofactors. -/
theorem add_coprime (f g : RationalFn K) (h : Cofactors f.den g.den) :
    Coprime (f.num * h.right + g.num * h.left) h.left ∧
      Coprime (f.num * h.right + g.num * h.left) h.right := by
  constructor
  · exact ((f.bezout.of_dvd_right h.left_dvd).symm.mul_right h.coprime).symm.add_mul
  · have hc := ((g.bezout.of_dvd_right h.right_dvd).symm.mul_right h.coprime.symm).symm
    have ha := hc.add_mul (r := f.num)
    have he : g.num * h.left + f.num * h.right = f.num * h.right + g.num * h.left := by grind
    rw [he] at ha
    exact ha

/-- Addition with cancellation restricted to the shared denominator factor. -/
@[expose]
def addCoreWith (plan : MulPlan K) (f g : RationalFn K) : RationalFn K :=
  let h := cancelWith plan f.den g.den g.den_ne_zero
  let t := plan.mul f.num h.right + plan.mul g.num h.left
  if t = 0 then 0 else
    let e := cancelWith plan t h.common (monic_ne_zero h.monic)
    have hed : e.common ∣ g.den :=
      dvd_trans ⟨e.right, e.right_spec⟩ ⟨h.right, h.right_spec⟩
    let d := exactWith plan g.den e.common hed
    have hd : g.den = e.common * d := exact_spec plan g.den e.common hed
    have hde : d = e.right * h.right := by
      apply DensePoly.mul_right_cancel (monic_ne_zero e.monic)
      have hh := h.right_spec
      have he := e.right_spec
      grind
    ofCoprime e.left (plan.mul h.left d)
      (by rw [plan.mul_eq]
          exact mul_monic (h.monic_left f.monic_den) (monic_of_mul e.monic (hd ▸ g.monic_den)))
      (by
        rw [plan.mul_eq, hde]
        have ht : Coprime t h.left ∧ Coprime t h.right := by
          dsimp only [t]
          rw [plan.mul_eq, plan.mul_eq]
          exact add_coprime f g h
        exact (ht.1.of_dvd e.left_dvd (dvd_refl_poly _)).mul_right
          (e.coprime.mul_right (ht.2.of_dvd e.left_dvd (dvd_refl_poly _))))

/-- The cancelled addition algorithm represents the sum of fractions. -/
theorem addCoreWith_spec (plan : MulPlan K) (f g : RationalFn K) :
    (addCoreWith plan f g).num * (f.den * g.den) =
      (f.num * g.den + g.num * f.den) * (addCoreWith plan f g).den := by
  let h := cancelWith plan f.den g.den g.den_ne_zero
  have hb := h.left_spec
  have hd := h.right_spec
  unfold addCoreWith
  dsimp only
  split
  · rename_i ht
    change 0 * (f.den * g.den) = (f.num * g.den + g.num * f.den) * 1
    rw [plan.mul_eq, plan.mul_eq] at ht
    change f.num * h.right + g.num * h.left = 0 at ht
    grind
  · dsimp only [ofCoprime]
    let t := plan.mul f.num h.right + plan.mul g.num h.left
    let e := cancelWith plan t h.common (monic_ne_zero h.monic)
    have he := e.left_spec
    have her := e.right_spec
    have hed : e.common ∣ g.den :=
      dvd_trans ⟨e.right, her⟩ ⟨h.right, hd⟩
    have hquot := exact_spec plan g.den e.common hed
    change e.left * (f.den * g.den) =
      (f.num * g.den + g.num * f.den) * plan.mul h.left (exactWith plan g.den e.common hed)
    rw [plan.mul_eq]
    have ht : t = f.num * h.right + g.num * h.left := by
      dsimp only [t]; rw [plan.mul_eq, plan.mul_eq]
    apply DensePoly.mul_right_cancel (monic_ne_zero e.monic)
    grind

/-- Addition with direct zero, polynomial, and equal-denominator branches. -/
@[expose]
def addWith (plan : MulPlan K) (f g : RationalFn K) : RationalFn K :=
  if f.num = 0 then g else if g.num = 0 then f else
  if f.den = g.den then normalizeWith plan (f.num + g.num) f.den f.den_ne_zero else
  if hf : f.den = 1 then
    ofCoprime (plan.mul f.num g.den + g.num) g.den g.monic_den (by
      rw [plan.mul_eq]
      have h := g.bezout.add_mul (r := f.num)
      have he : g.num + f.num * g.den = f.num * g.den + g.num := by grind
      rw [he] at h
      exact h)
  else if hg : g.den = 1 then
    ofCoprime (f.num + plan.mul g.num f.den) f.den f.monic_den (by
      rw [plan.mul_eq]; exact f.bezout.add_mul)
  else addCoreWith plan f g

instance : Add (RationalFn K) := ⟨addWith defaultPlan⟩

/-- Addition represents the sum of input fractions on every direct branch. -/
theorem addWith_spec (plan : MulPlan K) (f g : RationalFn K) :
    (addWith plan f g).num * (f.den * g.den) =
      (f.num * g.den + g.num * f.den) * (addWith plan f g).den := by
  unfold addWith
  split
  · rename_i hf
    grind
  · split
    · rename_i hg
      grind
    · split
      · rename_i hd
        have h := normalizeWith_spec plan (f.num + g.num) f.den f.den_ne_zero
        grind
      · split
        · rename_i hf
          dsimp only [ofCoprime]
          rw [plan.mul_eq]
          grind
        · split
          · rename_i hg
            dsimp only [ofCoprime]
            rw [plan.mul_eq]
            grind
          · exact addCoreWith_spec plan f g

/-- Default addition represents the sum of fractions. -/
theorem add_spec (f g : RationalFn K) :
    (f + g).num * (f.den * g.den) = (f.num * g.den + g.num * f.den) * (f + g).den :=
  addWith_spec defaultPlan f g

/-- Addition is independent of the supplied lawful plan. -/
theorem addWith_eq (plan : MulPlan K) (f g : RationalFn K) : addWith plan f g = f + g := by
  apply (eq_iff _ _).mpr
  apply DensePoly.mul_right_cancel (mul_ne_zero f.den_ne_zero g.den_ne_zero)
  have h := addWith_spec plan f g
  have h' := add_spec f g
  grind

/-- Subtraction uses addition's cancellation algorithm with a negated numerator. -/
@[expose]
def subWith (plan : MulPlan K) (f g : RationalFn K) : RationalFn K := addWith plan f (-g)

instance : Sub (RationalFn K) := ⟨subWith defaultPlan⟩

/-- Multiply after cancelling both cross gcds, before forming either product. -/
@[expose]
def mulWith (plan : MulPlan K) (f g : RationalFn K) : RationalFn K :=
  if f.num = 0 ∨ g.num = 0 then 0 else
    let u := cancelWith plan f.num g.den g.den_ne_zero
    let v := cancelWith plan g.num f.den f.den_ne_zero
    ofCoprime (plan.mul u.left v.left) (plan.mul v.right u.right)
      (by rw [plan.mul_eq]; exact mul_monic (v.monic_right f.monic_den) (u.monic_right g.monic_den))
      (by
        rw [plan.mul_eq, plan.mul_eq]
        exact Coprime.mul (f.bezout.of_dvd u.left_dvd v.right_dvd) u.coprime
          v.coprime (g.bezout.of_dvd v.left_dvd u.right_dvd))

instance : Mul (RationalFn K) := ⟨mulWith defaultPlan⟩

/-- Cancelled multiplication represents the product of its input fractions. -/
theorem mulWith_spec (plan : MulPlan K) (f g : RationalFn K) :
    (mulWith plan f g).num * (f.den * g.den) =
      (f.num * g.num) * (mulWith plan f g).den := by
  unfold mulWith
  split
  · rename_i h
    change 0 * (f.den * g.den) = f.num * g.num * 1
    rcases h with h | h <;> grind
  · dsimp only [ofCoprime]
    rw [plan.mul_eq, plan.mul_eq]
    have hu := (cancelWith plan f.num g.den g.den_ne_zero).left_spec
    have hud := (cancelWith plan f.num g.den g.den_ne_zero).right_spec
    have hv := (cancelWith plan g.num f.den f.den_ne_zero).left_spec
    have hvd := (cancelWith plan g.num f.den f.den_ne_zero).right_spec
    grind

/-- Multiplication represents the product of fractions. -/
theorem mul_spec (f g : RationalFn K) :
    (f * g).num * (f.den * g.den) = (f.num * g.num) * (f * g).den :=
  mulWith_spec defaultPlan f g

/-- Multiplication is independent of its lawful plan. -/
theorem mulWith_eq (plan : MulPlan K) (f g : RationalFn K) : mulWith plan f g = f * g := by
  apply (eq_iff _ _).mpr
  apply DensePoly.mul_right_cancel (mul_ne_zero f.den_ne_zero g.den_ne_zero)
  have h := mulWith_spec plan f g
  have h' := mul_spec f g
  grind

/-- Inversion swaps and rescales a nonzero pair without recomputing a gcd. -/
@[expose]
def inv (f : RationalFn K) : RationalFn K :=
  if h : f.num = 0 then 0 else
    if hm : f.num.leadingCoeff = 1 then
      ofCoprime f.den f.num hm f.bezout.symm
    else
    let c := f.num.leadingCoeff⁻¹
    have hc : c ≠ 0 := inv_ne_zero (leadingCoeff_ne_zero h)
    ofCoprime (scale c f.den) (scale c f.num)
      (by rw [scale_inv_eq_monicize h]; exact monicize_monic h)
      (((f.bezout.symm.scale_left hc).symm.scale_left hc).symm)

instance : Inv (RationalFn K) := ⟨inv⟩

/-- Inversion represents the reversed fraction for a nonzero input. -/
theorem inv_spec (f : RationalFn K) (hf : f.num ≠ 0) :
    f⁻¹.num * f.num = f.den * f⁻¹.den := by
  change (inv f).num * f.num = f.den * (inv f).den
  simp only [inv, hf, ↓reduceDIte, ofCoprime]
  split
  · rfl
  · dsimp only
    rw [scale_eq_C_mul, scale_eq_C_mul]
    grind

/-- Total inversion sends zero to zero. -/
@[simp]
theorem inv_zero : (0 : RationalFn K)⁻¹ = 0 := by rfl

/-- Divide using cancelled multiplication and total inversion. -/
@[expose]
def divWith (plan : MulPlan K) (f g : RationalFn K) : RationalFn K := mulWith plan f g⁻¹

instance : Div (RationalFn K) := ⟨divWith defaultPlan⟩

/-- Checked inversion rejects zero. -/
@[expose]
def inv? (f : RationalFn K) : Option (RationalFn K) :=
  if f.num = 0 then none else some f⁻¹

/-- Checked division rejects exactly a zero divisor. -/
@[expose]
def div? (f g : RationalFn K) : Option (RationalFn K) :=
  if g.num = 0 then none else some (f / g)

/-- Checked inversion fails exactly at zero. -/
theorem inv?_eq_none (f : RationalFn K) : inv? f = none ↔ f = 0 := by
  simp only [inv?, ← num_eq_zero]
  split <;> simp_all

/-- Checked division fails exactly at a zero divisor. -/
theorem div?_eq_none (f g : RationalFn K) : div? f g = none ↔ g = 0 := by
  simp only [div?, ← num_eq_zero]
  split <;> simp_all

/-- Polynomial powers by binary exponentiation using the supplied multiplication plan. -/
@[expose]
def polyPowWith (plan : MulPlan K) (p : DensePoly K) (n : Nat) : DensePoly K :=
  if n = 0 then 1 else if n = 1 then p else
    let r := polyPowWith plan (plan.square p) (n / 2)
    if n % 2 = 0 then r else plan.mul r p
termination_by n
decreasing_by omega

/-- Planned binary powering agrees with polynomial powering. -/
theorem polyPowWith_eq (plan : MulPlan K) (p : DensePoly K) (n : Nat) :
    polyPowWith plan p n = p ^ n := by
  induction n using Nat.strongRecOn generalizing p with
  | ind n ih =>
    change polyPowWith plan p n = natPow p n
    by_cases hn : n = 0
    · subst n; simp [polyPowWith]
    by_cases h1 : n = 1
    · subst n; simp [polyPowWith, natPow, Lean.Grind.Semiring.one_mul]
    · rw [polyPowWith, natPow]
      simp only [hn, h1, ↓reduceIte]
      rw [ih (n / 2) (by omega), plan.square_eq]
      split
      · rfl
      · rw [plan.mul_eq]; rfl

/-- Power the canonical numerator and denominator separately, without gcd computations. -/
@[expose]
def powWith (plan : MulPlan K) (f : RationalFn K) (n : Nat) : RationalFn K :=
  ofCoprime (polyPowWith plan f.num n) (polyPowWith plan f.den n)
    (by rw [polyPowWith_eq]; exact monic_pow f.monic_den n)
    (by rw [polyPowWith_eq, polyPowWith_eq]; exact f.bezout.pow n n)

instance : HPow (RationalFn K) Nat (RationalFn K) := ⟨powWith defaultPlan⟩

/-- Canonical powers have the powered numerator. -/
theorem num_pow (f : RationalFn K) (n : Nat) : (f ^ n).num = f.num ^ n :=
  polyPowWith_eq defaultPlan f.num n

/-- Canonical powers have the powered denominator. -/
theorem den_pow (f : RationalFn K) (n : Nat) : (f ^ n).den = f.den ^ n :=
  polyPowWith_eq defaultPlan f.den n

/-- Powers are independent of the supplied lawful plan. -/
theorem powWith_eq (plan : MulPlan K) (f : RationalFn K) (n : Nat) : powWith plan f n = f ^ n := by
  apply ext
  · exact (polyPowWith_eq plan f.num n).trans (num_pow f n).symm
  · exact (polyPowWith_eq plan f.den n).trans (den_pow f n).symm

/-- Subtraction is independent of its multiplication plan. -/
theorem subWith_eq (plan : MulPlan K) (f g : RationalFn K) :
    subWith plan f g = f - g := addWith_eq plan f (-g)

/-- Division is independent of its multiplication plan. -/
theorem divWith_eq (plan : MulPlan K) (f g : RationalFn K) :
    divWith plan f g = f / g := mulWith_eq plan f g⁻¹

/-- Checked inversion agrees with total inversion on nonzero inputs. -/
theorem inv?_eq_some (f : RationalFn K) (hf : f ≠ 0) : inv? f = some f⁻¹ := by
  simp only [inv?, num_eq_zero, hf, ↓reduceIte]

/-- Checked division agrees with total division for a nonzero divisor. -/
theorem div?_eq_some (f g : RationalFn K) (hg : g ≠ 0) : div? f g = some (f / g) := by
  simp only [div?, num_eq_zero, hg, ↓reduceIte]

end Hex.RationalFn
