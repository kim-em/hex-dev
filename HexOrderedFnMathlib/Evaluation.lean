/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexOrderedFnMathlib.Real
public import HexRationalFnMathlib.Correspondence

/-!
Injective real evaluation of canonical rational functions under transcendence
over the entire coefficient field.
-/

@[expose] public section

namespace Hex.OrderedFn.Real

open HexPolyMathlib
open scoped nonZeroDivisors
universe u
variable {K : Type u} [Field K] [DecidableEq K]

/-- No nonzero polynomial over the entire predecessor field vanishes at the
new constant under the specified coefficient embedding. -/
def RelativeTranscendence (ι : K →+* ℝ) (τ : ℝ) : Prop :=
  ∀ p : Polynomial K, p ≠ 0 → p.eval₂ ι τ ≠ 0

variable {ι : K →+* ℝ} {τ : ℝ}

omit [DecidableEq K] in
/-- A constant already in the predecessor field cannot be adjoined under the
relative-transcendence hypothesis, even if it is transcendental over the rationals. -/
theorem RelativeTranscendence.ne_image (h : RelativeTranscendence ι τ) (c : K) : τ ≠ ι c := by
  intro he
  have hn := h (Polynomial.X - Polynomial.C c) (Polynomial.X_sub_C_ne_zero c)
  apply hn
  simp [he]


omit [DecidableEq K] in
theorem RelativeTranscendence.preserves_nonzero (h : RelativeTranscendence ι τ) :
    (Polynomial K)⁰ ≤ (ℝ)⁰.comap (Polynomial.eval₂RingHom ι τ) := by
  intro p hp
  exact mem_nonZeroDivisors_iff_ne_zero.mpr
    (h p (mem_nonZeroDivisors_iff_ne_zero.mp hp))

/-- Evaluation at a relatively transcendental constant is a field embedding. -/
noncomputable def evalHom (h : RelativeTranscendence ι τ) : RationalFn K →+* ℝ :=
  (RatFunc.liftRingHom (Polynomial.eval₂RingHom ι τ) (h.preserves_nonzero)).comp
    HexRationalFnMathlib.equiv.toRingHom

theorem evalHom_apply (h : RelativeTranscendence ι τ) (f : RationalFn K) :
    evalHom h f = eval ι τ f := by
  change RatFunc.liftRingHom (Polynomial.eval₂RingHom ι τ) h.preserves_nonzero
    (HexRationalFnMathlib.toRatFunc f) = _
  rw [HexRationalFnMathlib.toRatFunc, HexRationalFnMathlib.embed,
    HexRationalFnMathlib.embed, RatFunc.liftRingHom_apply_div]
  rfl

theorem evalHom_injective (h : RelativeTranscendence ι τ) :
    Function.Injective (evalHom h) := (evalHom h).injective

theorem eval_den_ne_zero (h : RelativeTranscendence ι τ) (f : RationalFn K) :
    (toPolynomial f.den).eval₂ ι τ ≠ 0 := by
  apply h
  intro he
  apply f.den_ne_zero
  exact equiv.injective (he.trans (toPolynomial_zero).symm)

/-- Agreement with Mathlib's universe-zero evaluator; `evalHom` itself is universe-polymorphic. -/
theorem evalHom_eq_ratFunc {K : Type} [Field K] [DecidableEq K]
    {ι : K →+* ℝ} {τ : ℝ} (h : RelativeTranscendence ι τ) (f : RationalFn K) :
    evalHom h f = RatFunc.eval ι τ (HexRationalFnMathlib.toRatFunc f) := by
  rw [evalHom_apply, eval, HexRationalFnMathlib.num_toRatFunc,
    HexRationalFnMathlib.den_toRatFunc]
  rfl

@[simp] theorem evalHom_C (h : RelativeTranscendence ι τ) (c : K) :
    evalHom h (RationalFn.C c) = ι c := by
  rw [evalHom_apply]
  simp [eval, RationalFn.C, RationalFn.ofPoly]

@[simp] theorem evalHom_X (h : RelativeTranscendence ι τ) :
    evalHom h RationalFn.X = τ := by
  rw [evalHom_apply]
  simp [eval, RationalFn.X, RationalFn.ofPoly]

end Hex.OrderedFn.Real
