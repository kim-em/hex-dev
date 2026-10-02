/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

import HexRCF.RealCoefficients

open Hex Hex.RCF.RealCoefficients

set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

-- These inputs use the existing checked algebraic-number constructor rather
-- than `Selected.real`, including its erased canonicalization-success proof.
private abbrev cubicRep : RefinedIsolation CubeTwo.polynomial :=
  Field.literalRep CubeTwo.polynomial CubeTwo.square (by decide) (by decide)

private abbrev cubicAlgebraic : AlgebraicNumber :=
  AlgebraicNumber.ofNormalized CubeTwo.polynomial (by rfl) (by decide)
    (by decide) CubeTwo.checked CubeTwo.squarefree cubicRep
    (AlgebraicNumber.ofNormalized?_isSome _ _ _ _ _ _ _)

private def cubic : RealAlgebraicNumber :=
  RealAlgebraicNumber.ofAlgebraic cubicAlgebraic (by
    apply (AlgebraicNumber.isReal_iff _).mpr
    exact (congrArg Complex.im (Selected.normalized_toComplex
      CubeTwo.polynomial (by rfl) (by decide) (by decide)
      CubeTwo.checked CubeTwo.squarefree cubicRep _)).trans
      (Field.literalRep_real _ _ _ _ (by decide)))

private abbrev coordinate : QAdjoin cubic.toAlgebraic :=
  (cubic.toAlgebraic.toQAdjoin ^ 2 + 1) / 2

private abbrev coefficient : RealAlgebraicNumber :=
  Coefficients.ofField cubic coordinate

theorem normalized_positive : ∀ x : ℝ, x ^ 2 + cubic.toReal > 0 := by
  rcf

theorem normalized_section : ∃ x : ℝ,
    x ^ 2 = cubic.toReal ∧ 1 < x ∧ x < cubic.toReal := by
  rcf

theorem normalized_field : ∀ x : ℝ, x ^ 2 + coefficient.toReal > 0 := by
  rcf

theorem normalized_common : ∀ x : ℝ, x ^ 2 + cubic.toReal + Real.sqrt 2 > 0 := by
  rcf

private abbrev negativeSquare : DyadicSquare :=
  ⟨-SquareTwo.square.re, 0, SquareTwo.square.prec⟩

private abbrev negativeRep : RefinedIsolation SquareTwo.polynomial :=
  Field.literalRep SquareTwo.polynomial negativeSquare (by decide) (by decide)

private abbrev negativeAlgebraic : AlgebraicNumber :=
  AlgebraicNumber.ofNormalized SquareTwo.polynomial (by rfl) (by decide)
    (by decide) SquareTwo.checked SquareTwo.squarefree negativeRep
    (AlgebraicNumber.ofNormalized?_isSome _ _ _ _ _ _ _)

private def negative : RealAlgebraicNumber :=
  RealAlgebraicNumber.ofAlgebraic negativeAlgebraic (by
    apply (AlgebraicNumber.isReal_iff _).mpr
    exact (congrArg Complex.im (Selected.normalized_toComplex
      SquareTwo.polynomial (by rfl) (by decide) (by decide)
      SquareTwo.checked SquareTwo.squarefree negativeRep _)).trans
      (Field.literalRep_real _ _ _ _ (by decide)))

-- The equation alone does not select the positive conjugate. The original
-- negative square authenticates the different sign, through the same replay.
theorem normalized_negative : ∀ x : ℝ, x ^ 2 - negative.toReal > 0 := by
  rcf

/-- error: rcf: the universal sentence is false on the prepared cells -/
#guard_msgs in
example : ∀ x : ℝ, x ^ 2 + negative.toReal > 0 := by
  rcf

-- False results stay terminal, and the failed attempt restores tactic state.
example : True := by
  fail_if_success
    have : ∀ x : ℝ, x ^ 2 + cubic.toReal < 0 := by rcf
  have h : ∀ x : ℝ, x ^ 2 + cubic.toReal > 0 := by rcf
  trivial

-- Guard scanning still runs on the original source, before cancellation.
example : True := by
  fail_if_success
    have : ∀ x : ℝ, x + 0 / (cubic.toReal - cubic.toReal) = x := by rcf
  trivial

/-- info: '_private.HexRCF.NormalizedCoefficients.0.normalized_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms normalized_positive

/-- info: '_private.HexRCF.NormalizedCoefficients.0.normalized_section' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms normalized_section

/-- info: '_private.HexRCF.NormalizedCoefficients.0.normalized_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms normalized_field

/-- info: '_private.HexRCF.NormalizedCoefficients.0.normalized_common' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms normalized_common

/-- info: '_private.HexRCF.NormalizedCoefficients.0.normalized_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms normalized_negative
