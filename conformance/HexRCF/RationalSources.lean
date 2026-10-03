/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public meta import HexRCF.RealCoefficients
public meta import Lean.Elab.Command
public meta import Lean.Elab.Term

public section
namespace Hex.RCF.RationalSources
open Hex Lean Meta Qq
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

theorem positive : ∀ x : ℝ, x ^ 2 + (RealAlgebraicNumber.ofRat (3 / 2)).toReal > 0 := by rcf

theorem witness : ∃ x : ℝ, x = (RealAlgebraicNumber.ofRat (3 / 2)).toReal ∧ 1 < x ∧ x < 2 := by rcf

theorem reciprocal : ∀ x : ℝ, x / (RealAlgebraicNumber.ofRat (3 / 2)).toReal = (2 / 3) * x := by rcf

theorem mixed : ∀ x : ℝ,
    x ^ 2 + (RealAlgebraicNumber.ofRat (3 / 2)).toReal + Real.sqrt 2 > 0 := by rcf

run_meta do
  let source : Q(Prop) := q(∀ x : ℝ,
    x ^ 2 + (RealAlgebraicNumber.ofRat (3 / (2 + 1))).toReal > 0)
  let .ok data ← RealCoefficients.Reify.prepare source | throwError "source preparation failed"
  unless data.divisors.size == 1 && data.coefficients.isEmpty do
    throwError "rational payload guard was discarded or not lowered"
  checkWithKernel data.sentenceProof

-- Exercise refusal without admitting a proof of the false source. The helper
-- below checks a separate goal and returns the ordinary proof of True.
run_meta do
  let subject : Q(ℝ) := q(Real.sin (RealAlgebraicNumber.ofRat (3 / 2)).toReal)
  let source : Q(Prop) := q(∀ x : ℝ, x ^ 2 + $subject > 0)
  let .ok data ← RealCoefficients.Reify.prepare source {} #[subject] |
    throwError "registered source preparation failed"
  unless data.coefficients.size == 1 && data.coefficients[0]! == subject do
    throwError "registered whole subject identity was changed"
  checkWithKernel data.sentenceProof

local elab "refuse_source " source:term " expect " expected:str : tactic => do
  let target ← Lean.Elab.Term.elabTerm source (some (mkSort .zero))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let refused ← try
    let _ ← Hex.RCF.proveGoal target
    pure false
  catch error =>
    let message ← error.toMessageData.toString
    unless message.startsWith expected.getString do
      throwError "wrong refusal: {message}"
    pure true
  unless refused do throwError "expected terminal refusal"
  Lean.Elab.Tactic.closeMainGoal `refuse_source (mkConst ``True.intro)

example : True := by
  refuse_source (∀ x : ℝ, x ^ 2 + (RealAlgebraicNumber.ofRat (0 / (1 - 1))).toReal > 0)
    expect "rcf: original closed divisor is zero"

example : True := by
  refuse_source (∀ x : ℝ, 0 * (x / (RealAlgebraicNumber.ofRat 0).toReal) = 0)
    expect "rcf: original closed divisor is zero"

example : True := by
  refuse_source (∀ x : ℝ, x ^ 2 + (RealAlgebraicNumber.ofRat (-1)).toReal > 0)
    expect "rcf: the universal sentence is false"

example : True := by
  refuse_source (∀ x : ℝ, x ∈ Set.Ioc (1 : ℝ) 1 →
    0 * (x / (RealAlgebraicNumber.ofRat 0).toReal) = 0)
    expect "rcf: original closed divisor is zero"

/-- info: 'Hex.RCF.RationalSources.positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms positive
/-- info: 'Hex.RCF.RationalSources.witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms witness
/-- info: 'Hex.RCF.RationalSources.reciprocal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reciprocal
/-- info: 'Hex.RCF.RationalSources.mixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mixed
end Hex.RCF.RationalSources
