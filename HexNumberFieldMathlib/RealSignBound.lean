/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexNumberField.RealSign
public import HexNumberFieldMathlib.Roots
public import HexNumberFieldMathlib.CommonField

public section

namespace Hex.QAdjoin

/-- A real-part enclosure narrower than half the value's magnitude determines its sign. -/
theorem ballSign?_isSome (ball : DyadicComplexBall) (z : ℂ)
    (mem : z ∈ ball.set) (small : 2 * ball.realRadius < |z.re|) :
    (ballSign? ball).isSome = true := by
  have bound : |z.re - HexRootsMathlib.Dyadic.toReal ball.re| ≤ ball.realRadius := by
    have norm : ‖z - ball.center‖ ≤ ball.realRadius := by
      simpa only [DyadicComplexBall.set, Metric.mem_closedBall, dist_eq_norm] using mem
    exact (Complex.abs_re_le_norm (z - ball.center)).trans norm
  have radius : 0 ≤ ball.realRadius := (abs_nonneg _).trans bound
  by_cases positive : 0 < z.re
  · rw [abs_of_pos positive] at small
    have separated : HexRootsMathlib.Dyadic.toReal ball.radius <
        HexRootsMathlib.Dyadic.toReal ball.re := by
      have upper := (abs_le.mp bound).2
      change z.re - HexRootsMathlib.Dyadic.toReal ball.re ≤
        HexRootsMathlib.Dyadic.toReal ball.radius at upper
      change 2 * HexRootsMathlib.Dyadic.toReal ball.radius < z.re at small
      linarith
    simp [ballSign?, HexRootsMathlib.Dyadic.toReal_lt_toReal_iff.mp separated]
  · rw [abs_of_nonpos (le_of_not_gt positive)] at small
    have separated : HexRootsMathlib.Dyadic.toReal ball.re <
        HexRootsMathlib.Dyadic.toReal (-ball.radius) := by
      rw [HexRootsMathlib.Dyadic.toReal_neg]
      have lower := (abs_le.mp bound).1
      change -HexRootsMathlib.Dyadic.toReal ball.radius ≤
        z.re - HexRootsMathlib.Dyadic.toReal ball.re at lower
      change 2 * HexRootsMathlib.Dyadic.toReal ball.radius < -z.re at small
      linarith
    have negative := HexRootsMathlib.Dyadic.toReal_lt_toReal_iff.mp separated
    unfold ballSign?
    split <;> rfl

namespace SignApprox

/-- The evaluation eliminant is nonzero and vanishes at the selected coordinate. -/
theorem eliminant_spec (generator : AlgebraicNumber)
    (value : QAdjoin generator) :
    eliminant generator value ≠ 0 ∧
      (HexRootsMathlib.toPolyℂ (eliminant generator value)).IsRoot
        (PolyQuot.toComplex value generator.rep
          generator.rep_mk) := by
  let rep := generator.rep
  let h := generator.rep_mk
  let f : DensePoly (PolyQuot generator.p generator.x) :=
    DensePoly.ofList [-value, 1]
  let z := PolyQuot.toComplex value rep h
  have nonzero : !f.isZero := by
    have positive : 0 < f.size := by
      by_contra empty
      have coefficient := DensePoly.coeff_eq_zero_of_size_le f (i := 1) (by omega)
      have mapped := congrArg (fun a => PolyQuot.toComplex a rep h) coefficient
      have one : PolyQuot.toComplex (f.coeff 1) rep h = 1 := by
        change PolyQuot.toComplex
          ((DensePoly.ofList [-value, 1]).coeff 1) rep h = 1
        simpa [DensePoly.coeff_ofList, List.getD] using PolyQuot.map_one rep h
      have zero : PolyQuot.toComplex (Zero.zero : PolyQuot
          generator.p generator.x) rep h = 0 :=
        PolyQuot.map_zero rep h
      rw [one, zero] at mapped
      exact one_ne_zero mapped
    rw [(DensePoly.isZero_eq_false_iff f).mpr positive]
    rfl
  have linear : PolyQuot.toPolynomialAt f rep h =
      Polynomial.X - Polynomial.C z := by
    ext n
    rw [PolyQuot.coeff_toPolynomialAt, DensePoly.coeff_ofList]
    cases n with
    | zero =>
      simp only [List.getD, Polynomial.coeff_sub, Polynomial.coeff_X_zero,
        Polynomial.coeff_C_zero, zero_sub]
      exact PolyQuot.map_neg value rep h
    | succ n =>
      cases n with
      | zero =>
        simpa [List.getD, Polynomial.coeff_X] using PolyQuot.map_one rep h
      | succ n =>
        have zero : PolyQuot.toComplex (Zero.zero : PolyQuot
            generator.p generator.x) rep h = 0 :=
          PolyQuot.map_zero rep h
        simpa [List.getD, Polynomial.coeff_X, show n + 1 + 1 ≠ 1 by omega] using
          zero
  constructor
  · exact PolyQuot.Roots.normEliminant_ne_zero f nonzero
  · apply PolyQuot.Roots.normEliminant_isRoot f rep h z nonzero
    rw [linear, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]

/-- The finite endpoint always separates a nonconstant coordinate from zero. -/
theorem endpoint?_isSome (generator : AlgebraicNumber)
    (value : QAdjoin generator) (realGenerator : generator.isReal = true) (large : 1 < value.coeffs.size) :
    (endpoint? generator value).isSome = true := by
  let rep := generator.rep
  let h := generator.rep_mk
  let z := PolyQuot.toComplex value rep h
  let q := eliminant generator value
  let precision := evalDisambiguationLimit q 1
  let ball := (value.approx rep h (precision : Int)).2
  have mem : z ∈ ball.set := PolyQuot.approx_sound value rep h _
  have nonzero : z ≠ 0 := by
    intro zero
    have coordinate : value = 0 := PolyQuot.toComplex_injective rep h (by
      simpa only [PolyQuot.map_zero] using zero)
    subst value
    change 1 < (0 : DensePoly Rat).size at large
    simp at large
  have real : z.im = 0 := QAdjoin.value_real value realGenerator
  have cast : z = (z.re : ℂ) := Complex.ext rfl (by simp [real])
  have lower := ZPoly.normalizeEval_root_norm_lower
    (eliminant_spec generator value).1 nonzero (eliminant_spec generator value).2
  have realLower : ((q.evalLowerDenom : Nat) : ℝ)⁻¹ < |z.re| := by
    rw [cast] at lower
    simpa only [Complex.norm_real, Real.norm_eq_abs] using lower
  have budget : ball.realRadius ≤
      (Nat.max 1 1 : ℝ) * (2 : ℝ) ^ (-(evalDisambiguationLimit q 1 : Int)) := by
    simpa only [Nat.max_self, Nat.cast_one, one_mul] using
      (PolyQuot.approx_radius value rep h (precision : Int))
  have small := evalRadiusSmall_real (evalDisambiguationLimit_radius_small q 1 ball budget)
  have denom : 0 < (q.evalLowerDenom : ℝ) := by
    exact_mod_cast (show 0 < q.evalLowerDenom by unfold ZPoly.evalLowerDenom; omega)
  have triple : 3 * ball.realRadius < (q.evalLowerDenom : ℝ)⁻¹ := by
    rw [inv_eq_one_div]
    apply (lt_div_iff₀ denom).mpr
    simpa only [DyadicComplexBall.realRadius, mul_assoc, mul_comm, mul_left_comm] using small
  have radius : 0 ≤ ball.realRadius := by
    have norm : ‖z - ball.center‖ ≤ ball.realRadius := by
      simpa only [DyadicComplexBall.set, Metric.mem_closedBall, dist_eq_norm] using mem
    exact (norm_nonneg _).trans norm
  exact ballSign?_isSome ball z mem (by linarith)

end SignApprox

end Hex.QAdjoin
