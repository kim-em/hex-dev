/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexKronecker.Preflight
public import HexKroneckerMathlib.Saturation

public section
namespace Hex.Kronecker.Preflight

theorem clip_eq (bits n : Nat) : clip bits n = min n (2^bits) := by
  unfold clip
  by_cases hn : n = 0
  · simp [hn]
  · simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, hn, false_or, Nat.log2_lt hn]
    split_ifs with h
    · exact (min_eq_left (Nat.le_of_lt h)).symm
    · exact (min_eq_right (by omega)).symm

theorem add_eq (bits a b : Nat) : add bits a b = Saturating.add (2^bits) a b := by
  rw [add, clip_eq, Saturating.add_eq]

theorem mul_eq (bits a b : Nat) : mul bits a b = Saturating.mul (2^bits) a b := by
  rw [Saturating.mul_eq]
  unfold mul
  split_ifs with hz hbits
  · rcases Bool.or_eq_true_iff.mp hz with ha | hb
    · simp [eq_of_beq ha]
    · simp [eq_of_beq hb]
  · have ha : a ≠ 0 := by intro ha; simp [ha] at hz
    have hb : b ≠ 0 := by intro hb; simp [hb] at hz
    apply (min_eq_right _).symm
    calc
      2^bits ≤ 2^(a.log2 + b.log2) := Nat.pow_le_pow_right (by decide) hbits
      _ = 2^a.log2 * 2^b.log2 := Nat.pow_add _ _ _
      _ ≤ a*b := Nat.mul_le_mul (Nat.log2_self_le ha) (Nat.log2_self_le hb)
  · exact clip_eq bits (a*b)

theorem over_iff (bits n : Nat) : (n != 0 && bits ≤ n.log2) = true ↔ 2^bits ≤ n := by
  by_cases hn : n = 0
  · simp [hn]
  · simp [hn, Nat.le_log2 hn]

theorem powAux_eq (bits fuel a n : Nat) :
    powAux bits fuel a n = Saturating.powAux (2^bits) fuel a n := by
  induction fuel generalizing n with
  | zero => simp [powAux, Saturating.powAux, Nat.one_le_two_pow]
  | succ fuel ih =>
      simp only [powAux, Saturating.powAux, ih, over_iff, mul_eq]
      simp [Nat.one_le_two_pow]

theorem pow_eq (bits a n : Nat) : pow bits a n = Saturating.pow (2^bits) a n :=
  powAux_eq bits n a n

theorem sum_eq (bits : Nat) (a b : Bounds) : sum bits a b = a.add (2^bits) b := by
  simp only [sum, Bounds.add, add_eq]

theorem product_eq (bits : Nat) (a b : Bounds) : product bits a b = a.mul (2^bits) b := by
  simp only [product, Bounds.mul, mul_eq]

theorem power_eq (bits : Nat) (a : Bounds) (n : Nat) : power bits a n = a.pow (2^bits) n := by
  simp only [power, Bounds.pow, pow_eq]

theorem scan_eq (bits k : Nat) (e : Expr) : scan bits k e = e.scan (2^bits) k := by
  induction e <;> simp_all [scan, Expr.scan, clip_eq, sum_eq, product_eq, power_eq, Nat.one_le_two_pow]

theorem analyze_eq (bits k : Nat) (e : Expr) (acc : List Bounds) :
    analyze bits k e acc = e.analyze (2^bits) k acc := by
  simp only [analyze, Expr.analyze, scan_eq]

/-- Preserve every field of the public preflight, including saturated lower bounds. -/
theorem exprEq_eq (budget : Budget) (k : Nat) (lhs rhs : Expr) :
    exprEq budget k lhs rhs = sizeExprEq budget k lhs rhs := by
  simp only [exprEq, sizeExprEq, analyze_eq, sum_eq]

end Hex.Kronecker.Preflight
