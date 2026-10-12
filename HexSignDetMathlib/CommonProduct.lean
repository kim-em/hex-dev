/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.CommonProduct
public import HexPolyMathlib.Interpret
public import Mathlib.Algebra.Squarefree.Basic

public section

namespace Hex.SignDet

open HexPolyMathlib.Interpret

variable {E : Type u} {K : Type v} {Ctx : Type w}
variable [Zero E] [DecidableEq E] [Add E] [Sub E] [Mul E] [DecidableEq Ctx]
variable [Field K] [DecidableEq K]
variable (f : E → K) (hz : ∀ a, f a = 0 ↔ a = 0)
variable (ha : ∀ a b, f (a + b) = f a + f b)
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)

include ha hs hm in
/-- Arbitrary accepted common-product identities certify exactly the union
of the old root sets. This algebraic bridge needs neither a gcd semantic
premise nor a real-closed-field foundation; squarefreeness is checked separately. -/
theorem CommonProduct.check_roots {context : Ctx} {p q : DensePoly E}
    {c : CommonProduct E Ctx} (h : c.check context p q = true) (a : K) :
    (interpret f hz c.head).eval a = 0 ↔
      (interpret f hz p).eval a = 0 ∨ (interpret f hz q).eval a = 0 := by
  obtain ⟨_, hprod, hleft, hright⟩ := c.check_eq h
  have hp := (sub_isZero f hz hs _ _).mp hprod
  have hl := (sub_isZero f hz hs _ _).mp hleft
  have hr := (sub_isZero f hz hs _ _).mp hright
  simp only [interpret_mul f hz ha hm] at hp hl hr
  have ep := congrArg (Polynomial.eval a) hp
  have el := congrArg (Polynomial.eval a) hl
  have er := congrArg (Polynomial.eval a) hr
  simp only [Polynomial.eval_mul] at ep el er
  constructor
  · intro hh
    apply mul_eq_zero.mp
    rw [ep, hh, zero_mul]
  · rintro (hh | hh)
    · rw [el, hh, zero_mul]
    · rw [er, hh, zero_mul]

variable [One E] [Div E]
variable (hd : ∀ a b, f (a / b) = f a / f b)

/-- Division by an associated gcd constructs an associated lcm and the three
product/divisibility identities, including zero inputs. -/
private theorem quotient_lcm (p q g : Polynomial K)
    (hg : Associated g (EuclideanDomain.gcd p q)) :
    (p * q / g) * g = p * q ∧ p ∣ p * q / g ∧ q ∣ p * q / g ∧
      Associated (p * q / g) (EuclideanDomain.lcm p q) := by
  have hgp : g ∣ p := hg.dvd_iff_dvd_left.mpr (EuclideanDomain.gcd_dvd_left p q)
  have hgq : g ∣ q := hg.dvd_iff_dvd_left.mpr (EuclideanDomain.gcd_dvd_right p q)
  have hprod : (p * q / g) * g = p * q := by
    by_cases hg0 : g = 0
    · have hp0 : p = 0 := zero_dvd_iff.mp (hg0 ▸ hgp)
      simp only [hg0, hp0, zero_mul, EuclideanDomain.div_zero]
    · rw [mul_comm, EuclideanDomain.mul_div_cancel' hg0 (hgp.mul_right q)]
  have hleft : p ∣ p * q / g := ⟨q / g, EuclideanDomain.mul_div_assoc p hgq⟩
  have hright : q ∣ p * q / g := by
    rw [mul_comm p q]
    exact ⟨p / g, EuclideanDomain.mul_div_assoc q hgp⟩
  refine ⟨hprod, hleft, hright, ?_⟩
  by_cases hg0 : g = 0
  · have hp0 : p = 0 := zero_dvd_iff.mp (hg0 ▸ hgp)
    simp only [hp0, zero_mul, EuclideanDomain.zero_div, EuclideanDomain.lcm_zero_left]
    exact Associated.refl 0
  · apply Associated.of_mul_right (b := g) (d := EuclideanDomain.gcd p q) _ hg hg0
    rw [hprod, mul_comm (EuclideanDomain.lcm p q), EuclideanDomain.gcd_mul_lcm]
    exact Associated.refl _

include ha hs hm hd in
/-- The actual shared gcd/division constructor always passes its literal
identity checks. Its head is associated to the mathematical least common
multiple, including when one or both inputs are zero. Coefficient equality
need not reflect equality of their mathematical values. -/
theorem CommonProduct.build_success (context : Ctx) (p q : DensePoly E) :
    ∃ c : {c : CommonProduct E Ctx // c.check context p q = true},
      CommonProduct.build context p q = .ok c ∧
        Associated (interpret f hz c.val.head)
          (EuclideanDomain.lcm (interpret f hz p) (interpret f hz q)) := by
  let g := DensePoly.gcd p q
  let head := (DensePoly.divMod (p * q) g).1
  let c : CommonProduct E Ctx := ⟨context, p, q, head, g,
    (DensePoly.divMod head p).1, (DensePoly.divMod head q).1⟩
  have hquot (a b : DensePoly E) : interpret f hz (DensePoly.divMod a b).1 =
      interpret f hz a / interpret f hz b :=
    congrArg Prod.fst (interpret_divMod f hz hs hm hd a b)
  have hhead : interpret f hz head = interpret f hz p * interpret f hz q / interpret f hz g := by
    rw [hquot, interpret_mul f hz ha hm]
  obtain ⟨hprod, hleft, hright, hassoc⟩ := quotient_lcm (interpret f hz p) (interpret f hz q)
    (interpret f hz g) (interpret_gcd f hz hs hm hd p q)
  rw [← hhead] at hprod hleft hright hassoc
  have hcancel (a : Polynomial K) (had : a ∣ interpret f hz head) :
      a * (interpret f hz head / a) = interpret f hz head := by
    by_cases ha0 : a = 0
    · have hh0 : interpret f hz head = 0 := zero_dvd_iff.mp (ha0 ▸ had)
      simp only [ha0, hh0, zero_mul]
    · exact EuclideanDomain.mul_div_cancel' ha0 had
  have hc : c.check context p q = true := by
    simp only [CommonProduct.check, Bool.and_eq_true, decide_eq_true_eq, and_assoc]
    refine ⟨rfl, rfl, rfl, ?_, ?_, ?_⟩
    · apply (sub_isZero f hz hs _ _).mpr
      change interpret f hz (p * q) = interpret f hz (head * g)
      rw [interpret_mul f hz ha hm, interpret_mul f hz ha hm, hprod]
    · apply (sub_isZero f hz hs _ _).mpr
      change interpret f hz head = interpret f hz (p * (DensePoly.divMod head p).1)
      rw [interpret_mul f hz ha hm, hquot head p, hcancel _ hleft]
    · apply (sub_isZero f hz hs _ _).mpr
      change interpret f hz head = interpret f hz (q * (DensePoly.divMod head q).1)
      rw [interpret_mul f hz ha hm, hquot head q, hcancel _ hright]
  exact ⟨⟨c, hc⟩, CommonProduct.build_of_check context p q hc, hassoc⟩

include ha hs hm hd in
/-- The actual common head is nonzero and squarefree for squarefree inputs.
This supplies a valid whole-line prepared domain for root comparison. -/
theorem CommonProduct.build_squarefree (context : Ctx) (p q : DensePoly E)
    (hp : Squarefree (interpret f hz p)) (hq : Squarefree (interpret f hz q)) :
    ∃ c : {c : CommonProduct E Ctx // c.check context p q = true},
      CommonProduct.build context p q = .ok c ∧
        Squarefree (interpret f hz c.val.head) := by
  obtain ⟨c, hc, hassoc⟩ := CommonProduct.build_success f hz ha hs hm hd context p q
  have hn : EuclideanDomain.lcm (interpret f hz p) (interpret f hz q) ≠ 0 := by
    intro he
    exact ((EuclideanDomain.lcm_eq_zero_iff).mp he).elim hp.ne_zero hq.ne_zero
  have hr : IsRadical (EuclideanDomain.lcm (interpret f hz p) (interpret f hz q)) := by
    intro n x hx
    exact EuclideanDomain.lcm_dvd
      (hp.isRadical n x ((EuclideanDomain.dvd_lcm_left _ _).trans hx))
      (hq.isRadical n x ((EuclideanDomain.dvd_lcm_right _ _).trans hx))
  exact ⟨c, hc, hassoc.squarefree_iff.mpr (hr.squarefree hn)⟩

end Hex.SignDet
