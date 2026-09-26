/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import HexRCF.RealCoefficients

private abbrev cubicGenerator : Hex.AlgebraicNumber :=
  Hex.RCF.RealCoefficients.CubeTwo.realAlgebraic.toAlgebraic

private abbrev fieldCoordinate : Hex.QAdjoin cubicGenerator :=
  1 + cubicGenerator.toQAdjoin

private abbrev fieldCoefficient : Hex.RealAlgebraicNumber :=
  Hex.RCF.RealCoefficients.Coefficients.ofField
    Hex.RCF.RealCoefficients.CubeTwo.realAlgebraic fieldCoordinate

private abbrev literalCubic : Hex.RealAlgebraicNumber :=
  Hex.RCF.RealCoefficients.Selected.real
    Hex.RCF.RealCoefficients.CubeTwo.polynomial
    Hex.RCF.RealCoefficients.CubeTwo.square
    (by decide) (by decide) (by rfl) (by decide) (by decide)
    Hex.RCF.RealCoefficients.CubeTwo.checked
    Hex.RCF.RealCoefficients.CubeTwo.squarefree (by decide)

private abbrev literalSquare : Hex.RealAlgebraicNumber :=
  Hex.RCF.RealCoefficients.Selected.real
    Hex.RCF.RealCoefficients.SquareTwo.polynomial
    Hex.RCF.RealCoefficients.SquareTwo.square
    (by decide) (by decide) (by rfl) (by decide) (by decide)
    Hex.RCF.RealCoefficients.SquareTwo.checked
    Hex.RCF.RealCoefficients.SquareTwo.squarefree (by decide)

private abbrev genericGenerator : Hex.AlgebraicNumber := literalCubic.toAlgebraic

private abbrev genericCoordinate : Hex.QAdjoin genericGenerator :=
  (genericGenerator.toQAdjoin * genericGenerator.toQAdjoin + 1) / 2

private abbrev genericCoefficient : Hex.RealAlgebraicNumber :=
  Hex.RCF.RealCoefficients.Selected.field
    Hex.RCF.RealCoefficients.CubeTwo.polynomial
    Hex.RCF.RealCoefficients.CubeTwo.square
    (by decide) (by decide) (by rfl) (by decide) (by decide)
    Hex.RCF.RealCoefficients.CubeTwo.checked
    Hex.RCF.RealCoefficients.CubeTwo.squarefree (by decide) genericCoordinate

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

-- The optional import leaves rational `rcf` behavior intact.
example : ∀ x : ℝ, x ^ 2 + 1 > 0 := by
  rcf

-- Each algebraic goal starts with ordinary user notation and reaches the
-- selected-root identity, fixed-field sign certificates and kernel checker.
example : ∀ x : ℝ, x ^ 2 + Real.sqrt 2 > 0 := by
  rcf

example : ∀ x : ℝ, x ^ 2 + literalSquare.toReal > 0 := by
  rcf

example : ∃ x : ℝ, Real.sqrt 2 < x ∧ x < (3 : ℝ) / 2 := by
  rcf

theorem cubicRootDemo : ∀ x : ℝ, x ^ 2 + (2 : ℝ) ^ (1 / 3 : ℝ) > 0 := by
  rcf

/-- info: '_private.HexRCF.RealCoefficientTactic.0.cubicRootDemo' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms cubicRootDemo

example : ∀ x : ℝ,
    x ^ 2 + Hex.RCF.RealCoefficients.CubeTwo.realAlgebraic.toReal > 0 := by
  rcf

example : ∀ x : ℝ, x ^ 2 + literalCubic.toReal > 0 := by
  rcf

theorem algebraicWitnessDemo : ∃ x : ℝ, x ^ 2 = literalCubic.toReal := by
  rcf

/-- info: '_private.HexRCF.RealCoefficientTactic.0.algebraicWitnessDemo' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms algebraicWitnessDemo

theorem cubicIntervalDemo : ∃ x : ℝ,
    x ^ 2 = literalCubic.toReal ∧
    1 < x ∧ x < literalCubic.toReal := by
  rcf

/-- info: '_private.HexRCF.RealCoefficientTactic.0.cubicIntervalDemo' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms cubicIntervalDemo

example : ∀ x : ℝ, x ^ 2 + genericCoefficient.toReal > 0 := by
  rcf

example : ∀ x : ℝ,
    x ^ 2 + Hex.RCF.RealCoefficients.CubeTwo.shifted.toReal > 0 := by
  rcf

example : ∀ x : ℝ, x ^ 2 + fieldCoefficient.toReal > 0 := by
  rcf

example : True := by
  fail_if_success
    have : ∀ x : ℝ, x ^ 2 + Real.sqrt 2 < 0 := by rcf
  trivial

example : True := by
  fail_if_success
    have : ∀ x : ℝ, Real.sin x = 0 := by rcf
  trivial
