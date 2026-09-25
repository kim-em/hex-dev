/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.Isolations
public import HexRCF.RealCoefficients.Radical
public import HexRealAlgebraicMathlib.Order

public section

/-! Specialize checked cell isolation to canonical real algebraic coefficients. -/

namespace Hex.RCF.RealCoefficients.IsolationReplay

open HexPolyMathlib.Interpret HexRealRootsMathlib

/-- The executable comparison sign agrees with the real sign. -/
theorem algebraic_sign (a : RealAlgebraicNumber) :
    a.sign = (SignType.sign a.toReal : Int) := by
  rcases lt_trichotomy a.toReal 0 with hneg | hzero | hpos
  · simp [RealAlgebraicNumber.sign_eq, hneg, sign_neg hneg]
  · simp [RealAlgebraicNumber.sign_eq, hzero]
  · simp [RealAlgebraicNumber.sign_eq, hpos.ne',
      not_lt.mpr hpos.le, sign_pos hpos]

/-- Rational dyadic points have their expected real interpretation. -/
theorem dyadic_point (d : Dyadic) :
    (RealAlgebraicNumber.ofRat d.toRat).toReal = HexRealRootsMathlib.Dyadic.toReal d := by
  simp only [RealAlgebraicNumber.ofRat_toReal,
    HexRealRootsMathlib.toReal_eq_cast_toRat]

/-- A checked algebraic-coefficient isolation yields all real roots in order,
with ordinary open-cell sample membership. -/
theorem roots_algebraic {Ctx : Type u} [DecidableEq Ctx]
    (context : Ctx) (head : DensePoly RealAlgebraicNumber)
    (cert : IsolationReplay RealAlgebraicNumber Ctx)
    (checked : cert.check RealAlgebraicNumber.sign
      (fun d => RealAlgebraicNumber.ofRat d.toRat) context head = true) :
    ∃ root : Fin cert.isolations.intervals.size → ℝ,
      (∀ i, (interpret RealAlgebraicNumber.toReal
          RadicalCert.zero_iff head).IsRoot (root i) ∧
        HexRealRootsMathlib.Dyadic.toReal cert.isolations.intervals[i].lower < root i ∧
        root i < HexRealRootsMathlib.Dyadic.toReal cert.isolations.intervals[i].upper) ∧
      StrictMono root ∧
      (∀ x, (interpret RealAlgebraicNumber.toReal
          RadicalCert.zero_iff head).IsRoot x ↔ ∃ i, root i = x) ∧
      (∀ cut, Cell.Region root (.open cut)
        (HexRealRootsMathlib.Dyadic.toReal (cert.isolations.openPoint cut))) := by
  exact cert.check_roots RealAlgebraicNumber.toReal RadicalCert.zero_iff
    RealAlgebraicNumber.one_toReal RealAlgebraicNumber.add_toReal
    RealAlgebraicNumber.sub_toReal RealAlgebraicNumber.mul_toReal
    (fun n => by
      change (RealAlgebraicNumber.ofRat (n : Rat)).toReal = (n : ℝ)
      simp) RealAlgebraicNumber.sign algebraic_sign
    (fun d => RealAlgebraicNumber.ofRat d.toRat) dyadic_point
    context head checked

end Hex.RCF.RealCoefficients.IsolationReplay
