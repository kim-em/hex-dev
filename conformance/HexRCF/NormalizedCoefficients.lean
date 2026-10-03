/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public import HexRCF.NormalizedInputs
public import HexReflect.Session
public meta import HexRCF.RealCoefficients
public meta import HexRCF.NormalizedInputs
public meta import Qq
public meta import Lean.Elab.Term.TermElabM

open Hex Hex.RCF.RealCoefficients

set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

-- These inputs use the existing checked algebraic-number constructor rather
-- than `Selected.real`, including its erased canonicalization-success proof.
private def cubicRep : RefinedIsolation CubeTwo.polynomial :=
  ⟨⟨CubeTwo.square, .ofWitness (by decide)⟩, by decide⟩

private def cubicAlgebraic : AlgebraicNumber :=
  AlgebraicNumber.ofNormalized CubeTwo.polynomial (by rfl) (by decide)
    (by decide) CubeTwo.checked CubeTwo.squarefree cubicRep
    (AlgebraicNumber.ofNormalized?_isSome _ _ _ _ _ _ _)

private def cubic : RealAlgebraicNumber :=
  RealAlgebraicNumber.ofAlgebraic cubicAlgebraic (by
    apply (AlgebraicNumber.isReal_iff _).mpr
    exact (congrArg Complex.im (Selected.normalized_toComplex
      CubeTwo.polynomial (by rfl) (by decide) (by decide)
      CubeTwo.checked CubeTwo.squarefree cubicRep _)).trans
      ((HexRootsMathlib.RefinedIsolation.meetsRealAxis_iff cubicRep).mp (by decide)))

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

/-- error: rcf: the universal sentence is false on the prepared cells -/
#guard_msgs in
example : ∀ x : ℝ, x ^ 2 + cubic.toReal < 0 := by
  rcf

private abbrev negativeCoordinate : QAdjoin negative.toAlgebraic :=
  negative.toAlgebraic.toQAdjoin + 1

private abbrev negativeCoefficient : RealAlgebraicNumber :=
  Coefficients.ofField negative negativeCoordinate

theorem negative_field : ∀ x : ℝ, x ^ 2 - negativeCoefficient.toReal > 0 := by
  rcf

theorem common_conjugates : ∀ x : ℝ, x ^ 2 + negative.toReal + Real.sqrt 2 ≥ 0 := by
  rcf

/-- error: rcf: the universal sentence is false on the prepared cells -/
#guard_msgs in
example : ∀ x : ℝ, x ^ 2 + negative.toReal + Real.sqrt 2 > 0 := by
  rcf

-- The complete exposed constructor works across a module boundary.
theorem imported_positive : ∀ x : ℝ,
    x ^ 2 + Hex.RCF.NormalizedInputs.exposed.toReal > 0 := by
  rcf

-- Checked local coefficient equalities are substituted before classification.
theorem alias_positive (a : ℝ) (ha : a = Hex.RCF.NormalizedInputs.exposed.toReal) :
    ∀ x : ℝ, x ^ 2 + a > 0 := by
  rcf

theorem radical_aliases (a b : ℝ) (ha : a = Real.sqrt 2) (hb : Real.sqrt 3 = b) :
    ∀ x : ℝ, x ^ 2 + b - a > 0 := by
  rcf

private def selectedTwo : RealAlgebraicNumber :=
  Selected.real SquareTwo.polynomial SquareTwo.square (by decide) (by decide)
    (by rfl) (by decide) (by decide) SquareTwo.checked SquareTwo.squarefree (by decide)

theorem normalized_selected : ∀ x : ℝ,
    x ^ 2 + cubic.toReal + selectedTwo.toReal > 0 := by
  rcf

-- Executability alone does not authenticate a hidden isolation square.
/--
error: rcf: normalized source square must reduce to its literal encoding in the kernel
(kernel) declaration type mismatch, '_private.HexRCF.NormalizedCoefficients.0._example._proof_2' has type
  { re := Dyadic.ofInt 645 >>> 9, im := Dyadic.ofInt 0, prec := 12 } =
    { re := Dyadic.ofInt 645 >>> 9, im := Dyadic.ofInt 0, prec := 12 }
but it is expected to have type
  (↑RCF.NormalizedInputs.hiddenRep).square = { re := Dyadic.ofInt 645 >>> 9, im := Dyadic.ofInt 0, prec := 12 }
-/
#guard_msgs in
example : ∀ x : ℝ, x ^ 2 + Hex.RCF.NormalizedInputs.hidden.toReal > 0 := by
  rcf

open Lean Meta Qq in
local elab "mixedDecline%" : term => do
  let saved ← saveState
  let target := q(∀ x : ℝ,
    x ^ 2 + Hex.RCF.NormalizedInputs.hidden.toReal + Real.sqrt (1 / 2) > 0)
  let .ok source ← Reify.prepare target |
    throwError "mixed source must prepare before handler classification"
  unless source.coefficients.size == 2 do
    throwError "mixed source must expose both coefficients"
  let result ← CommonTactic.handle target
  saved.restore
  match result with
  | .declined => return q(True.intro)
  | _ => throwError "normalized/unsupported mixture must decline before construction"

-- The imported hidden square throws if constructed. An unsupported sibling
-- must decline before that check, so this catches interleaved classification.
example : True := mixedDecline%

open Lean Meta Qq in
local elab "guardRejection%" : term => do
  let .ok source ← Reify.prepare q(∀ x : ℝ,
    x + 0 / (cubic.toReal - cubic.toReal) = x) |
    throwError "cancelled guard source did not prepare"
  unless source.divisors.size == 1 do
    throwError "cancelled source divisor was omitted"
  Tactic.checkGuards source
  return q(True.intro)

-- Source preparation retains the cancelled divisor. Its guard checker
-- refuses the exact zero, independently of the quotient solver's coverage.
/-- error: rcf: could not prove a closed divisor nonzero -/
#guard_msgs in
example : True := guardRejection%

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

/-- info: '_private.HexRCF.NormalizedCoefficients.0.negative_field' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms negative_field

/-- info: '_private.HexRCF.NormalizedCoefficients.0.common_conjugates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms common_conjugates

/-- info: '_private.HexRCF.NormalizedCoefficients.0.imported_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms imported_positive

/-- info: '_private.HexRCF.NormalizedCoefficients.0.alias_positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms alias_positive

/-- info: '_private.HexRCF.NormalizedCoefficients.0.radical_aliases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms radical_aliases

/-- info: '_private.HexRCF.NormalizedCoefficients.0.normalized_selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms normalized_selected
