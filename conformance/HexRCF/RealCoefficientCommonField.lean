/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import HexRCF.RealCoefficients

open Hex

private abbrev squarePolynomial : Hex.ZPoly := Hex.DensePoly.ofList [-3, 0, 1]
private abbrev squareSelection : Hex.DyadicSquare :=
  ⟨(Dyadic.ofInt 7094) >>> (12 : Int), 0, 10⟩

private theorem squareChecked : squarePolynomial.CheckedIrreducible :=
  Hex.RCF.RealCoefficients.Field.checkedIrreducible squarePolynomial
    (.eisenstein 3 0) (by decide +kernel) (by decide)

private theorem squarefree : Hex.HasOnlySimpleRoots squarePolynomial := by
  have hne : squarePolynomial ≠ 0 := by decide
  letI : squarePolynomial.CheckedIrreducible := squareChecked
  exact (HexRootsMathlib.hasOnlySimpleRoots_iff_separable squarePolynomial hne).mpr
    (Hex.ZPoly.CheckedIrreducible.separable squarePolynomial)

private def selectedThree : Hex.RealAlgebraicNumber :=
  Hex.RCF.RealCoefficients.Selected.real squarePolynomial squareSelection
    (by decide +kernel) (by decide +kernel) (by rfl)
    (by decide) (by decide)
    squareChecked squarefree (by decide +kernel)

private abbrev generator : Hex.AlgebraicNumber := selectedThree.toAlgebraic

private abbrev shiftedCoordinate : Hex.QAdjoin generator :=
  1 + generator.toQAdjoin

private abbrev shiftedThree : Hex.RealAlgebraicNumber :=
  Hex.RCF.RealCoefficients.Coefficients.ofField selectedThree shiftedCoordinate

private abbrev selectedShiftedThree : Hex.RealAlgebraicNumber :=
  Hex.RCF.RealCoefficients.Selected.field squarePolynomial squareSelection
    (by decide +kernel) (by decide +kernel) (by rfl)
    (by decide) (by decide)
    squareChecked squarefree (by decide +kernel) shiftedCoordinate

set_option maxRecDepth 2048

set_option maxHeartbeats 5000000 in
theorem selected_and_sqrt :
    ∀ x : ℝ, x ^ 2 + selectedThree.toReal - Real.sqrt 2 > 0 := by
  rcf

set_option maxHeartbeats 5000000 in
theorem field_and_sqrt :
    ∀ x : ℝ, x ^ 2 + shiftedThree.toReal - Real.sqrt 2 > 0 := by
  rcf

set_option maxHeartbeats 5000000 in
theorem selected_field_and_sqrt :
    ∀ x : ℝ, x ^ 2 + selectedShiftedThree.toReal - Real.sqrt 2 > 0 := by
  rcf

/-- info: '_private.HexRCF.RealCoefficientCommonField.0.field_and_sqrt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms field_and_sqrt

/-- info: '_private.HexRCF.RealCoefficientCommonField.0.selected_field_and_sqrt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms selected_field_and_sqrt

/-- info: 'Hex.RCF.RealCoefficients.Selected.field_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RCF.RealCoefficients.Selected.field_eval
