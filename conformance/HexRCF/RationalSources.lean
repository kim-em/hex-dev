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

theorem dividedMixed : ∀ x : ℝ,
    x ^ 2 / (RealAlgebraicNumber.ofRat 2).toReal + Real.sqrt 2 + Real.sqrt 3 > 0 := by rcf

theorem nestedRoot : ∀ x : ℝ,
    x ^ 2 + Real.sqrt (RealAlgebraicNumber.ofRat 2).toReal > 0 := by rcf

theorem zeroRoot : ∀ x : ℝ,
    x ^ 2 + Real.sqrt (RealAlgebraicNumber.ofRat 0).toReal ≥ 0 := by rcf

theorem negativeRoot : ∀ x : ℝ,
    x ^ 2 + Real.sqrt (RealAlgebraicNumber.ofRat (-1)).toReal ≥ 0 := by rcf

run_meta do
  let source : Q(Prop) := q(∀ x : ℝ,
    x ^ 2 + (RealAlgebraicNumber.ofRat (3 / (2 + 1))).toReal > 0)
  let .ok data ← RealCoefficients.Reify.prepare source | throwError "source preparation failed"
  unless data.divisors.size == 1 && data.coefficients.isEmpty do
    throwError "rational payload guard was discarded or not lowered"
  checkWithKernel data.sentenceProof
  unless data.divisors[0]! == q(((2 + 1 : ℚ) : ℝ)) do
    throwError "rational payload retained the wrong divisor"
  if data.sentence.find? (·.isAppOfArity ``RealAlgebraicNumber.toReal 1) |>.isSome then
    throwError "rational constructor escaped lowering"

run_meta do
  let subject : Q(ℝ) := q(Real.sin (RealAlgebraicNumber.ofRat (3 / 2)).toReal)
  let source : Q(Prop) := q(∀ x : ℝ, x ^ 2 + $subject > 0)
  let .ok data ← RealCoefficients.Reify.prepare source {} #[subject] |
    throwError "registered source preparation failed"
  unless data.coefficients.size == 1 && data.coefficients[0]! == subject do
    throwError "registered whole subject identity was changed"
  checkWithKernel data.sentenceProof

run_meta do
  let subject : Q(ℝ) := q(Real.sin (RealAlgebraicNumber.ofRat (0 / (1 - 1))).toReal)
  let source : Q(Prop) := q(∀ x : ℝ, 0 * $subject + x ^ 2 ≥ 0)
  let .ok data ← RealCoefficients.Reify.prepare source {} #[subject] |
    throwError "registered payload source preparation failed"
  unless data.divisors.size == 1 && data.divisors[0]! == q(((1 - 1 : ℚ) : ℝ)) do
    throwError "registered zero payload guard was discarded"
  unless data.coefficients.size == 1 && data.coefficients[0]! == subject do
    throwError "registered zero payload identity was changed"

-- Check a separate source goal, then return only the ordinary proof of True.
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

example : True := by
  refuse_source (∃ x : ℝ, x ^ 2 + (RealAlgebraicNumber.ofRat (3 / 2)).toReal < 0)
    expect "rcf: the existential sentence is false"

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
/-- info: 'Hex.RCF.RationalSources.dividedMixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms dividedMixed
/-- info: 'Hex.RCF.RationalSources.nestedRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nestedRoot
/-- info: 'Hex.RCF.RationalSources.zeroRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zeroRoot
/-- info: 'Hex.RCF.RationalSources.negativeRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms negativeRoot
end Hex.RCF.RationalSources
