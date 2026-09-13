/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPolyMathlib.LiteralData
public import Mathlib.Tactic.FieldSimp

public section

/-! Polynomial literal identities checked by integer coefficient arithmetic. -/

namespace HexPolyMathlib

open Hex.Matrix.Lists HexMatrixMathlib Polynomial

/-- A polynomial with integer coefficients and one common denominator. -/
@[expose] noncomputable def blockPolynomial (s : Scaled) : Polynomial ℚ :=
  polynomialOfList (decodeList s)

/-- Interpret integer coefficient lists in the rational polynomial ring. -/
@[expose] noncomputable def integerPolynomial (xs : List Int) : Polynomial ℚ :=
  polynomialOfList (xs.map (fun z => (z : ℚ)))

theorem integerPolynomial_nil : integerPolynomial [] = 0 := rfl

theorem integerPolynomial_cons (x : Int) (xs : List Int) :
    integerPolynomial (x :: xs) = C (x : ℚ) + X * integerPolynomial xs := rfl

theorem integerPolynomial_add (xs ys : List Int) :
    integerPolynomial (add xs ys) = integerPolynomial xs + integerPolynomial ys := by
  induction xs generalizing ys with
  | nil => simp [add, integerPolynomial_nil]
  | cons x xs ih =>
    cases ys with
    | nil => simp [add, integerPolynomial_nil]
    | cons y ys =>
      simp only [add, Int.add_def, integerPolynomial_cons, ih, Int.cast_add, map_add]
      ring

theorem integerPolynomial_scale (a : Int) (xs : List Int) :
    integerPolynomial (scale a xs) = C (a : ℚ) * integerPolynomial xs := by
  induction xs with
  | nil => simp [scale, integerPolynomial_nil]
  | cons x xs ih =>
    change integerPolynomial ((a * x) :: scale a xs) = _
    rw [integerPolynomial_cons, integerPolynomial_cons, ih, Int.cast_mul, map_mul]
    ring

theorem integerPolynomial_mul (xs ys : List Int) :
    integerPolynomial (mul xs ys) = integerPolynomial xs * integerPolynomial ys := by
  induction xs with
  | nil => simp [mul, integerPolynomial_nil]
  | cons x xs ih =>
    rw [mul, integerPolynomial_add, integerPolynomial_scale]
    simp only [integerPolynomial_cons, Int.cast_zero, map_zero, zero_add, ih]
    ring

theorem blockPolynomial_scale (s : Scaled) :
    blockPolynomial s = C ((s.denom : ℚ)⁻¹) * integerPolynomial s.nums := by
  change polynomialOfList (s.nums.map (decodeScalar s.denom)) = _
  induction s.nums with
  | nil => simp [polynomialOfList, integerPolynomial_nil]
  | cons x xs ih =>
    simp only [List.map_cons, polynomialOfList, integerPolynomial_cons, decodeScalar,
      div_eq_mul_inv, map_mul] at *
    rw [ih]
    ring

theorem blockPolynomial_add (a b : Scaled) (ha : 0 < a.denom) (hb : 0 < b.denom) :
    blockPolynomial (Scaled.add a b) = blockPolynomial a + blockPolynomial b := by
  rw [blockPolynomial_scale, blockPolynomial_scale a, blockPolynomial_scale b]
  simp only [Scaled.add, integerPolynomial_add, integerPolynomial_scale, Nat.mul_eq, Nat.cast_mul,
    Int.ofNat_eq_natCast, Int.cast_natCast, mul_inv_rev, map_mul]
  have ha' : (a.denom : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt ha)
  have hb' : (b.denom : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hb)
  have hca : C ((a.denom : ℚ)⁻¹) * C (a.denom : ℚ) = (1 : Polynomial ℚ) := by
    rw [← map_mul, inv_mul_cancel₀ ha', map_one]
  have hcb : C ((b.denom : ℚ)⁻¹) * C (b.denom : ℚ) = (1 : Polynomial ℚ) := by
    rw [← map_mul, inv_mul_cancel₀ hb', map_one]
  linear_combination
    C ((a.denom : ℚ)⁻¹) * integerPolynomial a.nums * hcb +
    C ((b.denom : ℚ)⁻¹) * integerPolynomial b.nums * hca

theorem blockPolynomial_mul (a b : Scaled) :
    blockPolynomial (Scaled.mul a b) = blockPolynomial a * blockPolynomial b := by
  rw [blockPolynomial_scale, blockPolynomial_scale a, blockPolynomial_scale b]
  simp only [Scaled.mul, integerPolynomial_mul, Nat.mul_eq, Nat.cast_mul, mul_inv_rev, map_mul]
  ring

theorem blockPolynomial_neg (a : Scaled) : blockPolynomial a.neg = -blockPolynomial a := by
  rw [blockPolynomial_scale, blockPolynomial_scale a]
  simp only [Scaled.neg, integerPolynomial_scale, Int.cast_neg, Int.cast_one, map_neg, map_one]
  ring

theorem blockPolynomial_sub (a b : Scaled) (ha : 0 < a.denom) (hb : 0 < b.denom) :
    blockPolynomial (a.sub b) = blockPolynomial a - blockPolynomial b := by
  rw [Scaled.sub, blockPolynomial_add a b.neg ha hb, blockPolynomial_neg, sub_eq_add_neg]

theorem blockPolynomial_pow (a : Scaled) (n : Nat) :
    blockPolynomial (a.pow n) = blockPolynomial a ^ n := by
  induction n with
  | zero => simp [Scaled.pow, blockPolynomial, decodeList, decodeScalar, polynomialOfList]
  | succ n ih => rw [Scaled.pow, blockPolynomial_mul, ih, pow_succ]

/-- Cross products identify a rational coefficient list with a block. -/
theorem polynomialOfList_eq_block (xs : List ℚ) (a : Scaled) (ha : 0 < a.denom)
    (h : scaleRow a.denom xs a.nums = true) : polynomialOfList xs = blockPolynomial a :=
  congrArg polynomialOfList (scaleRow_sound a.denom xs a.nums ha h)

end HexPolyMathlib
