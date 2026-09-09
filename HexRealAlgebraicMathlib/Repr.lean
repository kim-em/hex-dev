/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealAlgebraicMathlib.Order

public section

/-! The decimal emitted by the canonical representation selects the original real root. -/

namespace Hex.AlgebraicNumber.Display

/-- Truncating a decimal changes its rational value by less than one decimal unit. -/
theorem decimalValue_error (q : Rat) (digits : Nat) :
    |((decimalValue q digits : Rat) : ℝ) - (q : ℝ)| < 1 / (10 : ℝ) ^ digits := by
  let scale := 10 ^ digits
  let n := decimalNumerator q digits
  have hs : (0 : ℝ) < scale := by dsimp [scale]; positivity
  have hd : (0 : ℝ) < q.den := by exact_mod_cast q.den_pos
  have hlo : (n : ℝ) * q.den ≤ (q.num.natAbs : ℝ) * scale := by
    exact_mod_cast Nat.div_mul_le_self (q.num.natAbs * scale) q.den
  have hhi : (q.num.natAbs : ℝ) * scale < ((n : ℝ) + 1) * q.den := by
    have h := Nat.lt_mul_div_succ (q.num.natAbs * scale) q.den_pos
    rw [Nat.mul_comm q.den] at h
    exact_mod_cast h
  have hl : (n : ℝ) / scale ≤ (q.num.natAbs : ℝ) / q.den :=
    (div_le_div_iff₀ hs hd).mpr hlo
  have hu : (q.num.natAbs : ℝ) / q.den < ((n : ℝ) + 1) / scale := by
    apply (div_lt_div_iff₀ hd hs).mpr
    simpa only [mul_comm] using hhi
  have he : |(n : ℝ) / scale - (q.num.natAbs : ℝ) / q.den| < 1 / (scale : ℝ) := by
    rw [abs_of_nonpos (sub_nonpos.mpr hl)]
    rw [add_div] at hu
    linarith
  unfold decimalValue
  split
  · rename_i hneg
    have hn : (q.num : ℝ) < 0 := by exact_mod_cast hneg
    have hnum : (q.num.natAbs : ℝ) = -(q.num : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_neg hn]
    change |((-((n : Rat) / (scale : Rat)) : Rat) : ℝ) - (q : ℝ)| < 1 / (10 : ℝ) ^ digits
    push_cast
    rw [Rat.cast_def q]
    rw [hnum] at he
    have heq : -((n : ℝ) / scale) - (q.num : ℝ) / q.den =
        -((n : ℝ) / scale - -(q.num : ℝ) / q.den) := by ring
    rw [heq, abs_neg]
    simpa only [scale, Nat.cast_pow, Nat.cast_ofNat] using he
  · rename_i hnonneg
    have hn : (0 : ℝ) ≤ q.num := by exact_mod_cast (le_of_not_gt hnonneg)
    have hnum : (q.num.natAbs : ℝ) = (q.num : ℝ) := by
      rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg hn]
    change |(((n : Rat) / (scale : Rat) : Rat) : ℝ) - (q : ℝ)| < 1 / (10 : ℝ) ^ digits
    push_cast
    rw [Rat.cast_def q]
    rw [hnum] at he
    simpa only [scale, Nat.cast_pow, Nat.cast_ofNat] using he

/-- The display precision makes one decimal unit no larger than the separation unit. -/
theorem digitsFor_bound (m : Nat) :
    1 / (10 : ℝ) ^ digitsFor m ≤ (2 : ℝ) ^ (-(m : ℤ)) := by
  have hd : m ≤ 3 * digitsFor m := by unfold digitsFor; omega
  have hp : (2 : ℝ) ^ m ≤ 10 ^ digitsFor m := calc
    (2 : ℝ) ^ m ≤ 2 ^ (3 * digitsFor m) := pow_le_pow_right₀ (by norm_num) hd
    _ = 8 ^ digitsFor m := by rw [pow_mul]; norm_num
    _ ≤ 10 ^ digitsFor m := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  rw [zpow_neg, zpow_natCast, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) hp

end Hex.AlgebraicNumber.Display

namespace Hex.RealAlgebraicNumber

open HexRootsMathlib AlgebraicNumber.Display

/-- The algebraic value of the nearest-root term emitted by the canonical real representation.
The rational coordinate is exactly the signed scaled integer used by `Display.decimal`;
the imaginary coordinate is omitted by the real branch of the printer. -/
@[expose] noncomputable def reprTerm (a : RealAlgebraicNumber) : AlgebraicNumber :=
  a.toAlgebraic.p.rootNear
    (decimalValue a.toAlgebraic.rep.1.square.re.toRat (digitsFor (mahlerPrec a.toAlgebraic.p)))

/-- The truncated decimal in the emitted nearest-root expression recovers the original value. -/
theorem reprTerm_eq (a : RealAlgebraicNumber) : a.reprTerm = a.toAlgebraic := by
  apply ZPoly.rootNear_of_close
  let s := a.toAlgebraic.rep.1.square
  let ε : ℝ := (2 : ℝ) ^ (-(mahlerPrec a.toAlgebraic.p : ℤ))
  have he : 0 < ε := zpow_pos (by norm_num) _
  have hp : (2 : ℝ) ^ (-s.prec) ≤ ε := by
    apply zpow_le_zpow_right₀ (by norm_num)
    have h := a.toAlgebraic.rep.property
    dsimp only [s]
    omega
  have hrad : DyadicSquare.radius s < ε * (1449 / 1024) := by
    have hsqrt : Real.sqrt 2 < (1449 / 1024 : ℝ) := by
      convert sqrt_two_lt_sqrt2Hi using 1
      norm_num [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]
    rw [DyadicSquare.radius_eq]
    exact (mul_lt_mul_of_pos_left hsqrt (zpow_pos (by norm_num) _)).trans_le
      (mul_le_mul_of_nonneg_right hp (by norm_num))
  have hc : ‖a.toAlgebraic.toComplex - HexRootsMathlib.DyadicSquare.center s‖ ≤ DyadicSquare.radius s := by
    have hm := RefinedIsolation.root_mem_closedDisc a.toAlgebraic.rep
    change a.toAlgebraic.toComplex ∈ DyadicSquare.closedDisc s at hm
    simpa only [DyadicSquare.closedDisc, Metric.mem_closedBall, dist_eq_norm] using hm
  have hr : |a.toReal - (s.re.toRat : ℝ)| ≤ DyadicSquare.radius s :=
    (Complex.abs_re_le_norm _).trans hc
  have hd := (decimalValue_error s.re.toRat (digitsFor (mahlerPrec a.toAlgebraic.p))).trans_le
    (digitsFor_bound (mahlerPrec a.toAlgebraic.p))
  have ht := abs_sub_le
    ((decimalValue s.re.toRat (digitsFor (mahlerPrec a.toAlgebraic.p)) : Rat) : ℝ)
    (s.re.toRat : ℝ) a.toReal
  rw [abs_sub_comm (s.re.toRat : ℝ) a.toReal] at ht
  have hclose :
      |((decimalValue s.re.toRat (digitsFor (mahlerPrec a.toAlgebraic.p)) : Rat) : ℝ) - a.toReal| <
        2 * (ε * (1449 / 1024)) := by
    change _ < ε at hd
    nlinarith
  simpa only [AlgebraicNumber.point, Rat.cast_zero, zero_mul, add_zero,
    ← ofReal_toReal, ← Complex.ofReal_ratCast, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] using hclose

/-- The constructor in every emitted real representation succeeds. -/
theorem repr_isSome (a : RealAlgebraicNumber) : (ofAlgebraic? a.reprTerm).isSome = true := by
  rw [reprTerm_eq, ofAlgebraic?_isSome]
  exact a.property

/-- The generated real expression returns the same subtype value and never takes its fallback. -/
theorem repr_roundtrip (a : RealAlgebraicNumber) :
    (ofAlgebraic? a.reprTerm).getD
      (Hex.panicWith zero "RealAlgebraicNumber.repr: nonreal result") = a := by
  have h : ofAlgebraic? a.reprTerm = some a := (ofAlgebraic?_eq_some _ _).mpr (reprTerm_eq a)
  rw [h, Option.getD_some]

end Hex.RealAlgebraicNumber
