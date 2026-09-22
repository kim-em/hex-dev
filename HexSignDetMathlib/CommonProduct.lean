/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDet.CommonProduct
public import HexPolyMathlib.Interpret

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

end Hex.SignDet
