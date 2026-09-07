/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRationalFn.Field

public section

namespace Hex.RationalFn

universe u
variable {K : Type u} [Lean.Grind.Field K] [DecidableEq K]
open DensePoly
attribute [local instance] Lean.Grind.Semiring.natCast

/-- Formal differentiation by the quotient rule, followed by normalization. -/
@[expose]
def derivativeWith (plan : MulPlan K) (f : RationalFn K) : RationalFn K :=
  normalizeWith plan
    (plan.mul f.num.derivative f.den - plan.mul f.num f.den.derivative)
    (plan.square f.den) (by rw [plan.square_eq]; exact mul_ne_zero f.den_ne_zero f.den_ne_zero)

/-- Formal derivative using the default multiplication plan. -/
@[expose]
def derivative (f : RationalFn K) : RationalFn K := derivativeWith defaultPlan f

/-- The derivative represents the formal quotient-rule fraction. -/
theorem derivativeWith_spec (plan : MulPlan K) (f : RationalFn K) :
    Represents (derivativeWith plan f)
      (f.num.derivative * f.den - f.num * f.den.derivative) (f.den * f.den) := by
  have h := normalizeWith_spec plan
    (plan.mul f.num.derivative f.den - plan.mul f.num f.den.derivative)
    (plan.square f.den) (by rw [plan.square_eq]; exact mul_ne_zero f.den_ne_zero f.den_ne_zero)
  change (derivativeWith plan f).num * plan.square f.den =
    (plan.mul f.num.derivative f.den - plan.mul f.num f.den.derivative) *
      (derivativeWith plan f).den at h
  rw [plan.mul_eq, plan.mul_eq, plan.square_eq] at h
  exact h

/-- The default derivative satisfies the quotient rule. -/
theorem derivative_spec (f : RationalFn K) : Represents (derivative f)
    (f.num.derivative * f.den - f.num * f.den.derivative) (f.den * f.den) :=
  derivativeWith_spec defaultPlan f

/-- The derivative is independent of its lawful multiplication plan. -/
theorem derivativeWith_eq (plan : MulPlan K) (f : RationalFn K) :
    derivativeWith plan f = derivative f :=
  (derivativeWith_spec plan f).eq (derivative_spec f) (mul_ne_zero f.den_ne_zero f.den_ne_zero)

/-- Differentiate any fraction presentation, even if it contains cancellable factors. -/
theorem Represents.derivative {f : RationalFn K} {p q : DensePoly K}
    (h : Represents f p q) : Represents (derivative f)
      (p.derivative * q - p * q.derivative) (q * q) := by
  have hd := congrArg DensePoly.derivative h
  simp only [DensePoly.derivative_mul] at hd
  have hs := derivative_spec f
  unfold Represents at *
  apply DensePoly.mul_right_cancel (mul_ne_zero f.den_ne_zero f.den_ne_zero)
  grind

/-- Compare canonical values using cross products of arbitrary presentations. -/
theorem Represents.eq_of_cross {f g : RationalFn K} {a b c d : DensePoly K}
    (hf : Represents f a b) (hg : Represents g c d)
    (hb : b ≠ 0) (hd : d ≠ 0) (h : a * d = c * b) : f = g := by
  apply (eq_iff _ _).mpr
  apply DensePoly.mul_right_cancel (mul_ne_zero hb hd)
  unfold Represents at hf hg
  grind

private theorem poly_derivative_add (p q : DensePoly K) :
    (p + q).derivative = p.derivative + q.derivative := by
  apply ext_coeff
  intro i
  simp only [coeff_derivative_semiring, coeff_add_semiring]
  grind

/-- Formal differentiation is additive in every characteristic. -/
theorem derivative_add (f g : RationalFn K) : derivative (f + g) = derivative f + derivative g := by
  have hl := ((represents_self f).add (represents_self g)).derivative
  have hr := (derivative_spec f).add (derivative_spec g)
  apply hl.eq_of_cross hr
    (mul_ne_zero (mul_ne_zero f.den_ne_zero g.den_ne_zero) (mul_ne_zero f.den_ne_zero g.den_ne_zero))
    (mul_ne_zero (mul_ne_zero f.den_ne_zero f.den_ne_zero) (mul_ne_zero g.den_ne_zero g.den_ne_zero))
  rw [poly_derivative_add, DensePoly.derivative_mul, DensePoly.derivative_mul,
    DensePoly.derivative_mul]
  grind

/-- Formal differentiation satisfies the Leibniz rule in every characteristic. -/
theorem derivative_mul (f g : RationalFn K) :
    derivative (f * g) = derivative f * g + f * derivative g := by
  have hl := ((represents_self f).mul (represents_self g)).derivative
  have hr := ((derivative_spec f).mul (represents_self g)).add
    ((represents_self f).mul (derivative_spec g))
  apply hl.eq_of_cross hr
    (mul_ne_zero (mul_ne_zero f.den_ne_zero g.den_ne_zero) (mul_ne_zero f.den_ne_zero g.den_ne_zero))
    (mul_ne_zero
      (mul_ne_zero (mul_ne_zero f.den_ne_zero f.den_ne_zero) g.den_ne_zero)
      (mul_ne_zero f.den_ne_zero (mul_ne_zero g.den_ne_zero g.den_ne_zero)))
  rw [DensePoly.derivative_mul, DensePoly.derivative_mul]
  grind

/-- Differentiation commutes with polynomial embedding. -/
theorem derivative_ofPoly (p : DensePoly K) : derivative (ofPoly p) = ofPoly p.derivative := by
  have h := (represents_ofPoly p).derivative
  apply h.eq _ (mul_ne_zero (monic_ne_zero monic_one) (monic_ne_zero monic_one))
  have hone : (1 : DensePoly K).derivative = 0 := derivative_C_semiring 1
  change p.derivative * (1 * 1) = (p.derivative * 1 - p * (1 : DensePoly K).derivative) * 1
  rw [hone]
  grind

/-- Constants have zero formal derivative. -/
theorem derivative_C (a : K) : derivative (C a) = 0 := by
  rw [C, derivative_ofPoly, derivative_C_semiring]
  rfl

/-- The indeterminate has formal derivative one. -/
theorem derivative_X : derivative (X : RationalFn K) = 1 := by
  rw [X, derivative_ofPoly]
  apply congrArg ofPoly
  apply ext_coeff
  intro i
  simp only [coeff_derivative_semiring, coeff_monomial]
  change (Nat.cast (i + 1) : K) * (if i + 1 = 1 then 1 else 0) = (DensePoly.C 1).coeff i
  rw [coeff_C]
  by_cases hi : i = 0
  · subst i
    simp only [Nat.zero_add, ite_true, Lean.Grind.Semiring.natCast_one]
    exact Lean.Grind.Semiring.mul_one 1
  · simp only [show ¬i + 1 = 1 by omega, hi, ite_false]
    exact Lean.Grind.Semiring.mul_zero _

end Hex.RationalFn
