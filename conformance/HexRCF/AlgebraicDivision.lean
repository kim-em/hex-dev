/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public import HexBerlekamp.IrreducibilityElab
public meta import HexBerlekampZassenhaus.FactorTactic
public meta import HexRCF.RealCoefficients

namespace Hex.RCF.AlgebraicDivision
open RealCoefficients

set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

/-- Source division is compiled in the authenticated selected field. -/
theorem quotient_identity : ∀ x : ℝ,
    x / Real.sqrt 2 = (Real.sqrt 2 / 2) * x := by rcf

theorem square_divisor : ∀ x : ℝ, x / Real.sqrt 4 = x / 2 := by rcf

theorem mixed_square_alias : ∀ x : ℝ,
    x ^ 2 + Real.sqrt 4 - Real.sqrt 2 > 0 := by rcf

theorem quotient_positive : ∀ x : ℝ,
    x ^ 2 + 1 / (Real.sqrt 2 + 1) > 0 := by rcf

theorem quotient_power : ∀ x : ℝ,
    x ^ 2 + 1 / (Real.sqrt 2 + 1) ^ 3 > 0 := by rcf

theorem independent_division : ∀ x : ℝ,
    x ^ 2 + 1 / (Real.sqrt 2 + Real.sqrt 3) > 0 := by rcf

theorem nested_division : ∀ x : ℝ,
    x / (1 / Real.sqrt 2) = Real.sqrt 2 * x := by rcf

theorem valid_cancelled_division : ∀ x : ℝ,
    x ^ 2 + 0 / (Real.sqrt 2 + 1) ≥ 0 := by rcf

theorem guarded_empty_domain : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 0 →
    x ^ 2 + 1 / (Real.sqrt 2 + 1) < 0 := by rcf

/-- The root-section replay supplies a further real root over the field
containing the authenticated quotient coefficient. -/
theorem quotient_section : ∃ x : ℝ,
    x ^ 2 = 1 / (Real.sqrt 2 + 1) ∧ 0 < x ∧ x < 1 := by rcf

private abbrev negativeSquare : DyadicSquare :=
  ⟨-SquareTwo.square.re, 0, SquareTwo.square.prec⟩
private abbrev negativeRoot : RealAlgebraicNumber :=
  Selected.real SquareTwo.polynomial negativeSquare
    (by decide) (by decide) (by rfl) (by decide) (by decide)
    SquareTwo.checked SquareTwo.squarefree (by decide)

theorem negative_quotient : ∀ x : ℝ,
    x ^ 2 - 1 / negativeRoot.toReal > 0 := by rcf

/-- error: rcf: the universal sentence is false on the prepared cells -/
#guard_msgs in
example : ∀ x : ℝ, x ^ 2 + 1 / negativeRoot.toReal > 0 := by rcf

private abbrev plasticPolynomial : ZPoly := DensePoly.ofList [-1, -1, 0, 1]
private abbrev plasticSquare : DyadicSquare :=
  ⟨Dyadic.ofInt 5426 >>> (12 : Int), 0, 12⟩
private theorem plasticChecked : plasticPolynomial.CheckedIrreducible :=
  ⟨(ZPoly.isIrreducible_iff plasticPolynomial).mpr (irreducibility plasticPolynomial),
    by decide⟩
private theorem plasticSquarefree : HasOnlySimpleRoots plasticPolynomial := by
  have hne : plasticPolynomial ≠ 0 := by decide
  let : plasticPolynomial.CheckedIrreducible := plasticChecked
  exact (HexRootsMathlib.hasOnlySimpleRoots_iff_separable plasticPolynomial hne).mpr
    (ZPoly.CheckedIrreducible.separable plasticPolynomial)
private abbrev plasticRep : RefinedIsolation plasticPolynomial :=
  Field.literalRep plasticPolynomial plasticSquare (by decide) (by decide)
private abbrev plasticAlgebraic : AlgebraicNumber :=
  AlgebraicNumber.ofNormalized plasticPolynomial (by rfl) (by decide) (by decide)
    plasticChecked plasticSquarefree plasticRep
    (AlgebraicNumber.ofNormalized?_isSome _ _ _ _ _ _ _)
private def alpha : RealAlgebraicNumber :=
  RealAlgebraicNumber.ofAlgebraic plasticAlgebraic (by
    apply (AlgebraicNumber.isReal_iff _).mpr
    exact (congrArg Complex.im (Selected.normalized_toComplex
      plasticPolynomial (by rfl) (by decide) (by decide)
      plasticChecked plasticSquarefree plasticRep _)).trans
      (Field.literalRep_real _ _ _ _ (by decide)))
private abbrev beta : RealAlgebraicNumber :=
  Coefficients.ofField alpha (alpha.toAlgebraic.toQAdjoin ^ 2 - 1)

/-- For the selected cubic root, its computed field coordinate is its reciprocal. -/
theorem cubic_reciprocal : ∀ x : ℝ, x / alpha.toReal = beta.toReal * x := by rcf

private abbrev directBeta : RealAlgebraicNumber :=
  RealAlgebraicNumber.ofAlgebraic
    (alpha.toAlgebraic.toQAdjoin ^ 2 - 1).toAlgebraicNumber (by
      rw [AlgebraicNumber.isReal_iff, QAdjoin.toAlgebraicNumber,
        PolyQuot.toAlgebraicNumber_toComplex]
      exact QAdjoin.value_real _ alpha.property)

theorem direct_cubic_reciprocal : ∀ x : ℝ,
    x / alpha.toReal = directBeta.toReal * x := by rcf

private abbrev directSelected : RealAlgebraicNumber :=
  RealAlgebraicNumber.ofAlgebraic
    (CubeTwo.realAlgebraic.toAlgebraic.toQAdjoin + 1).toAlgebraicNumber (by
      rw [AlgebraicNumber.isReal_iff, QAdjoin.toAlgebraicNumber,
        PolyQuot.toAlgebraicNumber_toComplex]
      exact QAdjoin.value_real _ CubeTwo.realAlgebraic.property)

/-- A lone directly converted coordinate must reach the new frontend even
when its selected generator belongs to the earlier single-coefficient path. -/
theorem direct_selected_positive : ∀ x : ℝ,
    x ^ 2 + directSelected.toReal > 0 := by rcf

/-- error: rcf: the universal sentence is false on the prepared cells -/
#guard_msgs in
example : ∀ x : ℝ, x / Real.sqrt 2 = Real.sqrt 2 * x := by rcf

/-- error: rcf: original closed divisor is zero -/
#guard_msgs in
example : ∀ x : ℝ, x / ((Real.sqrt 2 - Real.sqrt 2)⁻¹) = 0 := by rcf

/-- error: rcf: original closed divisor is zero -/
#guard_msgs in
example : ∀ x : ℝ, x ^ 2 + 0 / (0 * Real.sqrt 2) ≥ 0 := by rcf

/-- error: rcf: original closed divisor is zero -/
#guard_msgs in
example : ∀ x : ℝ, x ^ 2 + 0 / (Real.sqrt 2 - Real.sqrt 2) ≥ 0 := by rcf

/-- error: rcf: original closed divisor is zero -/
#guard_msgs in
example : ∀ x : ℝ, x ≤ 0 → 0 < x → 0 / (alpha.toReal - alpha.toReal) = 0 := by rcf

end Hex.RCF.AlgebraicDivision

/-- info: '_private.HexRCF.AlgebraicDivision.0.Hex.RCF.AlgebraicDivision.quotient_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.AlgebraicDivision.quotient_identity

/-- info: '_private.HexRCF.AlgebraicDivision.0.Hex.RCF.AlgebraicDivision.quotient_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.AlgebraicDivision.quotient_positive

/-- info: '_private.HexRCF.AlgebraicDivision.0.Hex.RCF.AlgebraicDivision.quotient_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.AlgebraicDivision.quotient_power

/-- info: '_private.HexRCF.AlgebraicDivision.0.Hex.RCF.AlgebraicDivision.independent_division' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.AlgebraicDivision.independent_division

/-- info: '_private.HexRCF.AlgebraicDivision.0.Hex.RCF.AlgebraicDivision.cubic_reciprocal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.AlgebraicDivision.cubic_reciprocal

/-- info: '_private.HexRCF.AlgebraicDivision.0.Hex.RCF.AlgebraicDivision.nested_division' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.AlgebraicDivision.nested_division

/-- info: '_private.HexRCF.AlgebraicDivision.0.Hex.RCF.AlgebraicDivision.valid_cancelled_division' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.AlgebraicDivision.valid_cancelled_division

/-- info: '_private.HexRCF.AlgebraicDivision.0.Hex.RCF.AlgebraicDivision.guarded_empty_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.AlgebraicDivision.guarded_empty_domain

/-- info: '_private.HexRCF.AlgebraicDivision.0.Hex.RCF.AlgebraicDivision.direct_cubic_reciprocal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.AlgebraicDivision.direct_cubic_reciprocal

/-- info: 'Hex.RCF.RealCoefficients.Field.value_neg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.Field.value_neg

/-- info: 'Hex.RCF.RealCoefficients.Field.value_pow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.Field.value_pow

/-- info: 'Hex.RCF.RealCoefficients.Field.coordinate_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.Field.coordinate_ne_zero

/-- info: 'Hex.RCF.RealCoefficients.Field.value_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.Field.value_ne_zero

/-- info: 'Hex.RCF.RealCoefficients.Field.value_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.Field.value_quotient

/-- info: '_private.HexRCF.AlgebraicDivision.0.Hex.RCF.AlgebraicDivision.direct_selected_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.AlgebraicDivision.direct_selected_positive

/-- info: '_private.HexRCF.AlgebraicDivision.0.Hex.RCF.AlgebraicDivision.quotient_section' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.AlgebraicDivision.quotient_section

/-- info: '_private.HexRCF.AlgebraicDivision.0.Hex.RCF.AlgebraicDivision.negative_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.AlgebraicDivision.negative_quotient

/-- info: '_private.HexRCF.AlgebraicDivision.0.Hex.RCF.AlgebraicDivision.square_divisor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.AlgebraicDivision.square_divisor

/-- info: '_private.HexRCF.AlgebraicDivision.0.Hex.RCF.AlgebraicDivision.mixed_square_alias' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.AlgebraicDivision.mixed_square_alias
