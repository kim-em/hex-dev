/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPolyMathlib.Euclid
public import HexPoly.Interpret

public section

/-!
Noninjective interpretation of executable polynomial representations.

The coefficient carrier has ordinary operations and a unique stored zero, but
need not have ring laws. The operation-only transfer lemmas compose with the
existing lawful-target correspondence; only the semantic target is a field.
-/
namespace HexPolyMathlib.Interpret

open Hex DensePoly

universe u v

variable {E : Type u} {K : Type v} [Zero E] [DecidableEq E]
variable [Field K] [DecidableEq K]
variable (f : E → K) (hz : ∀ x, f x = 0 ↔ x = 0)

/-- Interpret coefficients without identifying distinct stored nonzero values. -/
noncomputable def interpret (p : DensePoly E) : Polynomial K :=
  toPolynomial (DensePoly.Interpret.map f hz p)

@[simp] theorem coeff_interpret (p : DensePoly E) (i : Nat) :
    (interpret f hz p).coeff i = f (p.coeff i) := by
  simp [interpret]

@[simp] theorem interpret_zero : interpret f hz (0 : DensePoly E) = 0 := by
  simp [interpret]

/-- Zero reflection is sufficient; injectivity of the coefficient map is not needed. -/
theorem interpret_eq_zero (p : DensePoly E) : interpret f hz p = 0 ↔ p = 0 := by
  change toPolynomial (DensePoly.Interpret.map f hz p) = 0 ↔ _
  rw [← toPolynomial_zero]
  exact (equiv (R := K)).injective.eq_iff.trans (DensePoly.Interpret.map_eq_zero f hz p)

@[simp] theorem natDegree_interpret (p : DensePoly E) :
    (interpret f hz p).natDegree = p.natDegree := by
  simp [interpret, natDegree_toPolynomial]

@[simp] theorem leadingCoeff_interpret (p : DensePoly E) :
    (interpret f hz p).leadingCoeff = f p.leadingCoeff := by
  simp [interpret, leadingCoeff_toPolynomial, DensePoly.Interpret.map_leading]

theorem interpret_add [Add E] (ha : ∀ a b, f (a + b) = f a + f b)
    (p q : DensePoly E) :
    interpret f hz (p + q) = interpret f hz p + interpret f hz q := by
  rw [interpret, DensePoly.Interpret.map_add f hz ha, toPolynomial_add]
  rfl

theorem interpret_sub [Sub E] (hs : ∀ a b, f (a - b) = f a - f b)
    (p q : DensePoly E) :
    interpret f hz (p - q) = interpret f hz p - interpret f hz q := by
  rw [interpret, DensePoly.Interpret.map_sub f hz hs, toPolynomial_sub]
  rfl

theorem interpret_neg [Sub E] (hs : ∀ a b, f (a - b) = f a - f b)
    (p : DensePoly E) : interpret f hz (-p) = -(interpret f hz p) := by
  rw [interpret, DensePoly.Interpret.map_neg f hz hs, toPolynomial_neg]
  rfl

/-- A nonzero monicized representation has leading value one under interpretation. -/
theorem monicize_leading [Mul E] [Inv E]
    (hm : ∀ a b, f (a * b) = f a * f b) (hi : ∀ a, f a⁻¹ = (f a)⁻¹)
    (p : DensePoly E) (hp : p ≠ 0) :
    (interpret f hz (monicize p)).leadingCoeff = 1 := by
  rw [interpret, DensePoly.Interpret.map_monicize f hz hm hi, leadingCoeff_toPolynomial]
  exact DensePoly.monicize_monic (fun h => hp ((DensePoly.Interpret.map_eq_zero f hz p).mp h))

/-- A zero difference decides semantic equality, even for unequal stored polynomials. -/
theorem sub_isZero [Sub E] (hs : ∀ a b, f (a - b) = f a - f b)
    (p q : DensePoly E) :
    (p - q).isZero = true ↔ interpret f hz p = interpret f hz q := by
  rw [isZero_eq_true_iff, size_eq_zero_iff, ← interpret_eq_zero f hz (p - q),
    interpret_sub f hz hs, sub_eq_zero]

theorem interpret_mul [Add E] [Mul E]
    (ha : ∀ a b, f (a + b) = f a + f b)
    (hm : ∀ a b, f (a * b) = f a * f b) (p q : DensePoly E) :
    interpret f hz (p * q) = interpret f hz p * interpret f hz q := by
  rw [interpret, DensePoly.Interpret.map_mul f hz ha hm, toPolynomial_mul]
  rfl

theorem interpret_derivative [NatCast E] [Mul E]
    (hn : ∀ n : Nat, f (n : E) = (n : K))
    (hm : ∀ a b, f (a * b) = f a * f b) (p : DensePoly E) :
    interpret f hz p.derivative = (interpret f hz p).derivative := by
  rw [interpret, DensePoly.Interpret.map_derivative f hz hn hm, toPolynomial_derivative]
  rfl

theorem eval_interpret [Add E] [Mul E]
    (ha : ∀ a b, f (a + b) = f a + f b)
    (hm : ∀ a b, f (a * b) = f a * f b) (p : DensePoly E) (x : E) :
    (interpret f hz p).eval (f x) = f (p.eval x) := by
  rw [interpret, eval_toPolynomial]
  exact (DensePoly.Interpret.map_eval f hz ha hm p x).symm

variable [One E] [Add E] [Sub E] [Mul E] [Div E]
variable (hs : ∀ a b, f (a - b) = f a - f b)
variable (hm : ∀ a b, f (a * b) = f a * f b)
variable (hd : ∀ a b, f (a / b) = f a / f b)
include hs hm hd

/-- The interpreted remainder is Mathlib's remainder, including division by zero. -/
theorem interpret_rem (p q : DensePoly E) :
    interpret f hz (divMod p q).2 = interpret f hz p % interpret f hz q := by
  have h := congrArg Prod.snd (DensePoly.Interpret.map_divMod f hz hs hm hd p q)
  dsimp only at h
  change toPolynomial _ = _
  rw [h]
  exact toPolynomial_mod _ _

/-- Polynomial modulus notation has the same interpreted remainder. -/
theorem interpret_mod (p q : DensePoly E) :
    interpret f hz (p % q) = interpret f hz p % interpret f hz q :=
  interpret_rem f hz hs hm hd p q

/-- Both division outputs agree with Mathlib, including a zero divisor. -/
theorem interpret_divMod (p q : DensePoly E) :
    (interpret f hz (divMod p q).1, interpret f hz (divMod p q).2) =
      (interpret f hz p / interpret f hz q, interpret f hz p % interpret f hz q) := by
  apply Prod.ext
  · have h := congrArg Prod.fst (DensePoly.Interpret.map_divMod f hz hs hm hd p q)
    dsimp only at h
    change toPolynomial _ = _
    rw [h]
    let a := DensePoly.Interpret.map f hz p
    let b := DensePoly.Interpret.map f hz q
    change toPolynomial (divMod a b).1 = toPolynomial a / toPolynomial b
    by_cases hb : b = 0
    · rw [hb, divMod_eq_zero_self_of_size_zero a 0 size_zero]
      simp
    · have hb' : toPolynomial b ≠ 0 := by
        intro he
        apply hb
        apply (equiv (R := K)).injective
        simpa using he
      apply mul_right_cancel₀ hb'
      have hr := toPolynomial_mod a b
      change toPolynomial (divMod a b).2 = _ at hr
      have hc := congrArg toPolynomial (DivModLaws.divMod_spec a b)
      rw [toPolynomial_add, toPolynomial_mul] at hc
      change _ + toPolynomial (divMod a b).2 = _ at hc
      rw [hr] at hc
      have hc' := EuclideanDomain.div_add_mod (toPolynomial a) (toPolynomial b)
      rw [mul_comm] at hc'
      exact add_right_cancel (hc.trans hc'.symm)
  · exact interpret_rem f hz hs hm hd p q

/-- The raw gcd is associated to Mathlib's normalized gcd. -/
theorem interpret_gcd (p q : DensePoly E) :
    Associated (interpret f hz (gcd p q))
      (EuclideanDomain.gcd (interpret f hz p) (interpret f hz q)) := by
  rw [interpret, DensePoly.Interpret.map_gcd f hz hs hm hd]
  exact toPolynomial_gcd_associated _ _

/-- The actual extended gcd supplies the interpreted Bézout identity. -/
theorem interpret_bezout (ha : ∀ a b, f (a + b) = f a + f b)
    (h1 : f (1 : E) = 1) (p q : DensePoly E) :
    interpret f hz (xgcd p q).left * interpret f hz p +
      interpret f hz (xgcd p q).right * interpret f hz q =
        interpret f hz (xgcd p q).gcd := by
  have h := DensePoly.Interpret.map_xgcd f hz hs hm hd ha h1 p q
  have hl := congrArg XGCDResult.left h
  have hr := congrArg XGCDResult.right h
  have hg := congrArg XGCDResult.gcd h
  dsimp only at hl hr hg
  unfold interpret
  rw [hl, hr, hg]
  exact toPolynomial_xgcd_bezout_raw _ _

end HexPolyMathlib.Interpret
