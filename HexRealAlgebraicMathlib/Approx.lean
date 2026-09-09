/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealAlgebraicMathlib.Order

public section

/-! Certified dyadic approximation and the enclosures used for rounding. -/

namespace Hex.RealAlgebraicNumber

open HexRootsMathlib

/-- The error in the real centre is bounded by the radius of the canonical disc. -/
theorem approx_error (a : RealAlgebraicNumber) (prec : Int) :
    |a.toReal - Dyadic.toReal (a.approx prec)| ≤ (a.approxBall prec).realRadius := by
  have h := AlgebraicNumber.approx_mem a.toAlgebraic prec
  have hn : ‖a.toAlgebraic.toComplex - (a.approxBall prec).center‖ ≤
      (a.approxBall prec).realRadius := by
    simpa only [approxBall, DyadicComplexBall.set, Metric.mem_closedBall, dist_eq_norm] using h
  have hr := Complex.abs_re_le_norm
    (a.toAlgebraic.toComplex - (a.approxBall prec).center)
  exact le_trans hr hn

/-- Approximation has the requested error bound, including negative precision. -/
theorem approx_bound (a : RealAlgebraicNumber) (prec : Int) :
    |a.toReal - Dyadic.toReal (a.approx prec)| ≤ (2 : ℝ) ^ (-prec) :=
  (approx_error a prec).trans (AlgebraicNumber.approx_radius a.toAlgebraic prec)

/-- The rational endpoints of the disc's real projection enclose the real value. -/
theorem approx_enclosure (a : RealAlgebraicNumber) (prec : Int) :
    (((a.approxBall prec).re.toRat - (a.approxBall prec).radius.toRat : Rat) : ℝ) ≤ a.toReal ∧
    a.toReal ≤ (((a.approxBall prec).re.toRat + (a.approxBall prec).radius.toRat : Rat) : ℝ) := by
  have h := abs_le.mp (approx_error a prec)
  change -((a.approxBall prec).radius.toRat : ℝ) ≤
      a.toReal - ((a.approxBall prec).re.toRat : ℝ) ∧
    a.toReal - ((a.approxBall prec).re.toRat : ℝ) ≤
      ((a.approxBall prec).radius.toRat : ℝ) at h
  push_cast
  constructor <;> linarith

/-- The precision-two enclosure used by floor has width at most one half. -/
theorem rounding_width (a : RealAlgebraicNumber) :
    (((a.approxBall 2).re.toRat + (a.approxBall 2).radius.toRat : Rat) : ℝ) -
      (((a.approxBall 2).re.toRat - (a.approxBall 2).radius.toRat : Rat) : ℝ) ≤ 1 / 2 := by
  have h := AlgebraicNumber.approx_radius a.toAlgebraic 2
  change ((a.approxBall 2).radius.toRat : ℝ) ≤ (2 : ℝ) ^ (-(2 : Int)) at h
  norm_num at h
  push_cast
  linarith

end Hex.RealAlgebraicNumber
