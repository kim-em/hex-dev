/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRationalFnMathlib.Correspondence
public import Mathlib.FieldTheory.RatFunc.AsPolynomial

public section

namespace HexRationalFnMathlib

universe u
variable {K : Type u} [Field K] [DecidableEq K]
open Hex

/-- Mathlib's total evaluation uses the same canonical coefficient arrays. -/
theorem eval_toRatFunc (f : RationalFn K) (a : K) :
    RatFunc.eval (RingHom.id K) a (toRatFunc f) = f.num.eval a / f.den.eval a := by
  rw [RatFunc.eval, ← num_toRatFunc, ← den_toRatFunc]
  simp only [Polynomial.eval₂_id, HexPolyMathlib.eval_toPolynomial]

/-- Partial evaluation agrees with Mathlib only together with canonical-denominator regularity. -/
theorem eval?_eq_some (f : RationalFn K) (a v : K) :
    RationalFn.eval? f a = some v ↔ (HexPolyMathlib.toPolynomial f.den).eval a ≠ 0 ∧
      v = RatFunc.eval (RingHom.id K) a (toRatFunc f) := by
  rw [RationalFn.eval?_eq_some, HexPolyMathlib.eval_toPolynomial, eval_toRatFunc]
  rfl

/-- A pole is a failed partial evaluation even though Mathlib's total evaluator returns zero. -/
theorem eval?_eq_none (f : RationalFn K) (a : K) :
    RationalFn.eval? f a = none ↔ (HexPolyMathlib.toPolynomial f.den).eval a = 0 := by
  rw [RationalFn.eval?_eq_none, HexPolyMathlib.eval_toPolynomial]
  simp only [RationalFn.Regular, not_not]

/-- At poles, Mathlib's total evaluation is zero. -/
theorem eval_eq_zero_of_none (f : RationalFn K) (a : K) (h : RationalFn.eval? f a = none) :
    RatFunc.eval (RingHom.id K) a (toRatFunc f) = 0 := by
  have hd := (eval?_eq_none f a).mp h
  rw [HexPolyMathlib.eval_toPolynomial] at hd
  rw [eval_toRatFunc, hd, div_zero]

/-- A raw input denominator may be used for evaluation only where it does not vanish. -/
theorem eval?_normalize (p q : DensePoly K) (hq : q ≠ 0) (a : K)
    (ha : (HexPolyMathlib.toPolynomial q).eval a ≠ 0) :
    RationalFn.eval? (RationalFn.normalize p q hq) a =
      some ((HexPolyMathlib.toPolynomial p).eval a / (HexPolyMathlib.toPolynomial q).eval a) := by
  simpa only [HexPolyMathlib.eval_toPolynomial] using
    RationalFn.eval?_normalize p q hq a (by simpa only [HexPolyMathlib.eval_toPolynomial] using ha)

end HexRationalFnMathlib
