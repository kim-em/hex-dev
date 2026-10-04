/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberFieldMathlib.RealSignBound
public import HexNumberFieldMathlib.Nearest
public section
namespace Hex.QAdjoin
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

/-- Successful checked signs agree with the selected real embedding. -/
theorem signApprox?_spec {generator : AlgebraicNumber} (value : QAdjoin generator)
    (real : generator.isReal = true) (sign : Int)
    (accepted : signApprox? value = some sign) :
    sign = (SignType.sign (PolyQuot.toComplex value generator.rep generator.rep_mk).re : Int) := by
  simp only [signApprox?, real, ite_true] at accepted
  split at accepted
  · rename_i small
    cases Option.some.inj accepted
    have constant : value.coeffs = DensePoly.C (value.coeffs.coeff 0) := by
      apply DensePoly.ext_coeff
      intro i
      rw [DensePoly.coeff_C]
      split
      · subst i
        rfl
      · exact DensePoly.coeff_eq_zero_of_size_le _ (by omega)
    rw [PolyQuot.toComplex, constant, HexPolyMathlib.toPolynomial_C, Polynomial.eval₂_C]
    have castSign : (SignType.sign (value.coeffs.coeff 0 : ℝ) : Int) =
        (if value.coeffs.coeff 0 < 0 then -1
          else if value.coeffs.coeff 0 = 0 then 0 else 1) := by
      rw [← scalarSign_eq]
      norm_cast
    simpa [DensePoly.coeff_C] using castSign.symm
  · split at accepted
    · rename_i probe hit
      cases Option.some.inj accepted
      apply ballSign?_spec _ _ _ _ (by simpa only [SignApprox.initial?] using hit)
      exact DyadicComplexBall.evalRatBall_mem _ _ _
        (DyadicComplexBall.mem_toBall
          (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc _))
    · split at accepted
      · rename_i probe hit
        cases Option.some.inj accepted
        exact ballSign?_spec _ _ _ (PolyQuot.approx_sound value _ _ _)
          (by simpa only [SignApprox.refined?] using hit)
      · exact ballSign?_spec _ _ _ (PolyQuot.approx_sound value _ _ _)
          (by simpa only [SignApprox.endpoint?] using accepted)

/-- The checked algorithm succeeds for every coordinate of a real generator. -/
theorem signApprox?_isSome {generator : AlgebraicNumber} (value : QAdjoin generator)
    (real : generator.isReal = true) : (signApprox? value).isSome = true := by
  simp only [signApprox?, real, ite_true]
  split
  · rfl
  · rename_i large
    split
    · rfl
    · split
      · rfl
      · exact SignApprox.endpoint?_isSome generator value real (by omega)

/-- The total operation has no reachable fallback on its stated domain. -/
theorem signApprox_spec {generator : AlgebraicNumber} (value : QAdjoin generator)
    (real : generator.isReal = true) :
    signApprox value real =
      (SignType.sign (PolyQuot.toComplex value generator.rep generator.rep_mk).re : Int) := by
  obtain ⟨sign, accepted⟩ := Option.isSome_iff_exists.mp (signApprox?_isSome value real)
  simp only [signApprox, accepted, Option.getD_some]
  exact signApprox?_spec value real sign accepted

/-- The interval strategy agrees with canonical comparison to zero. -/
theorem signApprox_eq {generator : AlgebraicNumber} (value : QAdjoin generator)
    (real : generator.isReal = true) :
    orderOfSign (signApprox value real) = value.toAlgebraicNumber.realCompare 0 := by
  have mapped : value.toAlgebraicNumber.toComplex =
      PolyQuot.toComplex value generator.rep generator.rep_mk :=
    PolyQuot.toAlgebraicNumber_toComplex value generator.rep generator.rep_mk
  have valueReal : value.toAlgebraicNumber.isReal = true := by
    apply (AlgebraicNumber.isReal_iff _).mpr
    rw [mapped]
    exact value_real value real
  rw [signApprox_spec, AlgebraicNumber.realCompare_eq _ _ valueReal
    ((AlgebraicNumber.isReal_iff _).mpr (by simp [AlgebraicNumber.zero_toComplex])),
    AlgebraicNumber.zero_toComplex]
  rw [mapped]
  let x := (PolyQuot.toComplex value generator.rep generator.rep_mk).re
  change compare (SignType.sign x : Int) 0 = compare x 0
  rcases lt_trichotomy x 0 with negative | zero | positive
  · rw [sign_eq_neg_one_iff.mpr negative]
    rw [compare_lt_iff_lt.mpr negative]
    decide
  · rw [zero]
    simp
  · rw [sign_eq_one_iff.mpr positive]
    rw [compare_gt_iff_gt.mpr positive]
    decide

end Hex.QAdjoin

/-- info: 'Hex.QAdjoin.signApprox?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.QAdjoin.signApprox?_isSome

/-- info: 'Hex.QAdjoin.signApprox_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.QAdjoin.signApprox_eq

/-- info: 'Hex.QAdjoin.SignApprox.endpoint?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.QAdjoin.SignApprox.endpoint?_isSome
