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

set_option maxRecDepth 2048
set_option maxHeartbeats 1000000

-- The optional import leaves rational `rcf` behavior intact.
example : ∀ x : ℝ, x ^ 2 + 1 > 0 := by
  rcf

-- Each algebraic goal starts with ordinary user notation and reaches the
-- selected-root identity, fixed-field sign certificates and kernel checker.
example : ∀ x : ℝ, x ^ 2 + Real.sqrt 2 > 0 := by
  rcf

example : ∃ x : ℝ, Real.sqrt 2 < x ∧ x < (3 : ℝ) / 2 := by
  rcf

example : ∀ x : ℝ, x ^ 2 + (2 : ℝ) ^ (1 / 3 : ℝ) > 0 := by
  rcf

example : ∀ x : ℝ,
    x ^ 2 + Hex.RCF.RealCoefficients.CubeTwo.realAlgebraic.toReal > 0 := by
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
