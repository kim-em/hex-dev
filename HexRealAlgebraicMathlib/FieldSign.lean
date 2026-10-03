/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealAlgebraic.FieldSign
public import HexRealAlgebraicMathlib.FieldSignBound
public import HexRealAlgebraicMathlib.Order
public import HexNumberFieldMathlib.Approx
public import HexNumberFieldMathlib.CommonField

public section

namespace Hex.RealAlgebraicNumber

/-- A successful disc probe gives the mathematical sign of the real part. -/
theorem ballSign?_spec (ball : DyadicComplexBall) (z : ℂ) (sign : Int)
    (mem : z ∈ ball.set) (accepted : ballSign? ball = some sign) :
    sign = (SignType.sign z.re : Int) := by
  have bound : |z.re - HexRootsMathlib.Dyadic.toReal ball.re| ≤ ball.realRadius := by
    have norm : ‖z - ball.center‖ ≤ ball.realRadius := by
      simpa only [DyadicComplexBall.set, Metric.mem_closedBall, dist_eq_norm] using mem
    exact (Complex.abs_re_le_norm (z - ball.center)).trans norm
  unfold ballSign? at accepted
  split at accepted
  · rename_i positive
    cases Option.some.inj accepted
    have separated := HexRootsMathlib.Dyadic.toReal_lt_toReal_iff.mpr positive
    have hz : 0 < z.re := by
      have := (abs_le.mp bound).1
      change -HexRootsMathlib.Dyadic.toReal ball.radius ≤
        z.re - HexRootsMathlib.Dyadic.toReal ball.re at this
      change HexRootsMathlib.Dyadic.toReal ball.radius <
        HexRootsMathlib.Dyadic.toReal ball.re at separated
      change |z.re - HexRootsMathlib.Dyadic.toReal ball.re| ≤
        HexRootsMathlib.Dyadic.toReal ball.radius at bound
      linarith
    rw [sign_eq_one_iff.mpr hz]
    rfl
  · split at accepted
    · rename_i negative
      cases Option.some.inj accepted
      have separated := HexRootsMathlib.Dyadic.toReal_lt_toReal_iff.mpr negative
      have hz : z.re < 0 := by
        have := (abs_le.mp bound).2
        change z.re - HexRootsMathlib.Dyadic.toReal ball.re ≤
          HexRootsMathlib.Dyadic.toReal ball.radius at this
        rw [HexRootsMathlib.Dyadic.toReal_neg] at separated
        change |z.re - HexRootsMathlib.Dyadic.toReal ball.re| ≤
          HexRootsMathlib.Dyadic.toReal ball.radius at bound
        linarith
      rw [sign_eq_neg_one_iff.mpr hz]
      rfl
    · contradiction

private theorem scalarSign_eq (x : ℝ) :
    (if x < 0 then (-1 : Int) else if x = 0 then 0 else 1) =
      (SignType.sign x : Int) := by
  split
  · rename_i h
    rw [sign_eq_neg_one_iff.mpr h]
    rfl
  · split
    · rename_i h
      subst x
      simp
    · rename_i h
      rw [sign_eq_one_iff.mpr (by order)]
      rfl

/-- The interval-based field sign agrees with the selected real embedding. -/
theorem signField_spec (generator : RealAlgebraicNumber)
    (value : QAdjoin generator.toAlgebraic) :
    signField generator value =
      (SignType.sign
        (PolyQuot.toComplex value generator.toAlgebraic.rep
          generator.toAlgebraic.rep_mk).re : Int) := by
  unfold signField
  dsimp only
  split
  · rename_i small
    have constant : value.coeffs = DensePoly.C (value.coeffs.coeff 0) := by
      apply DensePoly.ext_coeff
      intro i
      rw [DensePoly.coeff_C]
      split
      · subst i
        rfl
      · exact DensePoly.coeff_eq_zero_of_size_le _ (by omega)
    rw [PolyQuot.toComplex, constant, HexPolyMathlib.toPolynomial_C,
      Polynomial.eval₂_C]
    have castSign : (SignType.sign (value.coeffs.coeff 0 : ℝ) : Int) =
        (if value.coeffs.coeff 0 < 0 then -1
          else if value.coeffs.coeff 0 = 0 then 0 else 1) := by
      rw [← scalarSign_eq]
      norm_cast
    simpa [DensePoly.coeff_C] using castSign.symm
  · split
    · rename_i sign accepted
      apply ballSign?_spec _ _ _ _ (by simpa only [FieldSign.initial?] using accepted)
      exact DyadicComplexBall.evalRatBall_mem _ _ _
        (DyadicComplexBall.mem_toBall
          (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc _))
    · split
      · rename_i sign accepted
        exact ballSign?_spec _ _ _ (PolyQuot.approx_sound value _ _ _)
          (by simpa only [FieldSign.refined?] using accepted)
      · split
        · rename_i sign accepted
          exact ballSign?_spec _ _ _ (PolyQuot.approx_sound value _ _ _)
            (by simpa only [FieldSign.endpoint?] using accepted)
        · rename_i rejected
          have success := FieldSign.endpoint?_isSome generator value (by omega)
          simp only [rejected, Option.isSome_none, Bool.false_eq_true] at success

/-- The fast sign equals the existing canonical sign for every real field coordinate. -/
theorem signField_eq (generator : RealAlgebraicNumber)
    (value : QAdjoin generator.toAlgebraic)
    (real : value.toAlgebraicNumber.isReal = true) :
    signField generator value = (ofAlgebraic value.toAlgebraicNumber real).sign := by
  rw [signField_spec, sign_eq, scalarSign_eq]
  congr 2
  exact (congrArg Complex.re (PolyQuot.toAlgebraicNumber_toComplex value _ _)).symm

end Hex.RealAlgebraicNumber
