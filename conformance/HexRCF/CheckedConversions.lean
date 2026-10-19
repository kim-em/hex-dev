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
public meta import HexRCF.ProofEvidence
public meta import Mathlib.Tactic.NormNum.RealSqrt

public section

namespace Hex.RCF.CheckedConversions
open Hex RealCoefficients Lean Meta Qq

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem selected_value : ∀ x : ℝ,
    x + ((RealAlgebraicNumber.ofAlgebraic? CubeTwo.realAlgebraic.toAlgebraic).getD
      (RealAlgebraicNumber.ofRat 0)).toReal = x + CubeTwo.realAlgebraic.toReal := by rcf

theorem rational_fallback : ∃ x : ℝ,
    x = ((RealAlgebraicNumber.ofAlgebraic? AlgebraicNumber.I).getD
      (RealAlgebraicNumber.ofRat (3 / 2))).toReal ∧ 1 < x ∧ x < 2 := by rcf

theorem algebraic_fallback : ∀ x : ℝ,
    x + ((RealAlgebraicNumber.ofAlgebraic? AlgebraicNumber.I).getD
      CubeTwo.realAlgebraic).toReal = x + CubeTwo.realAlgebraic.toReal := by rcf

theorem nested_conversion : ∀ x : ℝ,
    x ^ 2 + ((RealAlgebraicNumber.ofAlgebraic?
      ((RealAlgebraicNumber.ofAlgebraic? AlgebraicNumber.I).getD
        CubeTwo.realAlgebraic).toAlgebraic).getD (RealAlgebraicNumber.ofRat 0)).toReal > 0 := by rcf

theorem selected_projection : ∀ x : ℝ,
    x ^ 2 + CubeTwo.realAlgebraic.toAlgebraic.re.toReal > 0 := by rcf

theorem imaginary_projection : ∀ x : ℝ,
    x ^ 2 + AlgebraicNumber.I.re.toReal ≥ 0 := by rcf

theorem original_divisor : ∀ x : ℝ,
    x ^ 2 / ((RealAlgebraicNumber.ofAlgebraic? AlgebraicNumber.I).getD
      (RealAlgebraicNumber.ofRat 2)).toReal + Real.sqrt 2 + Real.sqrt 3 > 0 := by rcf

theorem algebraic_divisor : ∀ x : ℝ,
    x / ((RealAlgebraicNumber.ofAlgebraic? AlgebraicNumber.I).getD
      CubeTwo.realAlgebraic).toReal = (CubeTwo.realAlgebraic.toReal ^ 2 / 2) * x := by rcf

theorem radical_conversion : ∀ x : ℝ,
    x ^ 2 + Real.sqrt ((RealAlgebraicNumber.ofAlgebraic? AlgebraicNumber.I).getD
      (RealAlgebraicNumber.ofRat 2)).toReal > 0 := by rcf

theorem checked_rational : ∃ x : ℝ,
    x = ((RealAlgebraicNumber.ofAlgebraic? (AlgebraicNumber.ofRat (3 / 2))).getD
      CubeTwo.realAlgebraic).toReal ∧ 1 < x ∧ x < 2 := by rcf

theorem unused_algebraic_divisor : ∀ x : ℝ,
    x ^ 2 + ((RealAlgebraicNumber.ofAlgebraic? (AlgebraicNumber.ofRat 1)).getD
      (1 / CubeTwo.realAlgebraic)).toReal > 0 := by rcf

theorem converted_radical_divisor : ∀ x : ℝ,
    x ^ 2 / Real.sqrt (RealAlgebraicNumber.ofRat 2).toReal + 1 > 0 := by rcf

theorem rational_radicals : ∀ x : ℝ,
    x ^ 2 + Real.sqrt (1 / 4) + Real.sqrt (9 / 4) > 0 := by rcf

theorem field_conversion : ∀ x : ℝ,
    x ^ 2 + ((RealAlgebraicNumber.ofAlgebraic?
      (CubeTwo.realAlgebraic.toAlgebraic.toQAdjoin ^ 2 - 1).toAlgebraicNumber).getD
      (RealAlgebraicNumber.ofRat 0)).toReal > 0 := by rcf

theorem field_projection : ∀ x : ℝ,
    x ^ 2 + (CubeTwo.realAlgebraic.toAlgebraic.toQAdjoin ^ 2 - 1).toAlgebraicNumber.re.toReal
      > 0 := by rcf

theorem nonreal_projection : ∀ x : ℝ,
    x ^ 2 + (CubeTwo.realAlgebraic.toAlgebraic + AlgebraicNumber.I).re.toReal > 0 := by rcf

theorem computed_power : ∀ x : ℝ,
    x ^ 2 + (CubeTwo.realAlgebraic ^ 2 - 1).toReal > 0 := by rcf

theorem computed_product : ∀ x : ℝ,
    x ^ 2 + (CubeTwo.realAlgebraic * CubeTwo.realAlgebraic).toReal > 0 := by rcf

theorem computed_inverse : ∀ x : ℝ,
    x / CubeTwo.realAlgebraic.toReal = CubeTwo.realAlgebraic⁻¹.toReal * x := by rcf

theorem computed_negative : ∀ x : ℝ,
    x ^ 2 - (-CubeTwo.realAlgebraic⁻¹).toReal > 0 := by rcf

theorem direct_division : ∀ x : ℝ,
    x ^ 2 + (RealAlgebraicNumber.div (RealAlgebraicNumber.ofRat 3)
      (RealAlgebraicNumber.ofRat 2)).toReal > 0 := by rcf

theorem integer_casts : ∀ x : ℝ,
    x ^ 2 + (4 : RealAlgebraicNumber).toReal + ((-3 : Int) : RealAlgebraicNumber).toReal > 0 := by rcf

theorem direct_power : ∀ x : ℝ,
    x ^ 2 + (RealAlgebraicNumber.natPow CubeTwo.realAlgebraic 2).toReal > 0 := by rcf

theorem direct_radical_base : ∀ x : ℝ,
    x ^ 2 + Real.sqrt (RealAlgebraicNumber.add (RealAlgebraicNumber.ofRat 1)
      (RealAlgebraicNumber.ofRat 1)).toReal > 0 := by rcf

theorem coerced_radical : ∀ x : ℝ,
    x ^ 2 + Real.sqrt ((RealAlgebraicNumber.ofAlgebraic?
      (AlgebraicNumber.ofReal (RealAlgebraicNumber.ofRat 2))).getD
        (RealAlgebraicNumber.ofRat 0)).toReal > 0 := by rcf

theorem coerced_divisor : ∀ x : ℝ,
    x ^ 2 / ((RealAlgebraicNumber.ofAlgebraic?
      (↑(RealAlgebraicNumber.ofRat 2) : AlgebraicNumber)).getD
        (RealAlgebraicNumber.ofRat 0)).toReal + Real.sqrt 2 > 0 := by rcf

theorem field_divisor : ∀ x : ℝ,
    x ^ 2 + ((RealAlgebraicNumber.ofAlgebraic?
      ((CubeTwo.realAlgebraic.toAlgebraic.toQAdjoin ^ 2 - 1) / 2).toAlgebraicNumber).getD
        (RealAlgebraicNumber.ofRat 0)).toReal > 0 := by rcf

set_option rcf.algebraic.reducedLiterals true in
theorem reduced_quotation : ∀ x : ℝ,
    x ^ 2 + CubeTwo.realAlgebraic.toReal > 0 := by rcf

run_meta do
  let subject : Q(ℝ) := q(Real.sin ((RealAlgebraicNumber.ofAlgebraic? AlgebraicNumber.I).getD
    (RealAlgebraicNumber.ofRat (3 / 2))).toReal)
  let source : Q(Prop) := q(∀ x : ℝ, x ^ 2 + $subject > 0)
  let .ok data ← Reify.prepare source {} #[subject] |
    throwError "registered conversion preparation failed"
  unless data.coefficients.size == 1 && data.coefficients[0]! == subject do
    throwError "registered conversion subject was rewritten"
  checkWithKernel data.sentenceProof

run_meta do
  let source : Q(Prop) := q(∀ x : ℝ,
    x ^ 2 + ((RealAlgebraicNumber.ofAlgebraic? CubeTwo.realAlgebraic.toAlgebraic).getD
      (RealAlgebraicNumber.ofRat (3 / 2))).toReal > 0)
  let .ok data ← Reify.prepare source | throwError "checked source preparation failed"
  unless data.coefficients.size == 1 &&
      data.coefficients[0]! == q(CubeTwo.realAlgebraic.toReal) do
    throwError "checked conversion changed the selected value"
  unless data.divisors.size == 1 && data.divisors[0]! == q(((2 : ℚ) : ℝ)) do
    throwError "unused fallback lost its original rational guard"
  checkWithKernel data.sentenceProof

-- Check a separate source; the enclosing example proves only True.
local elab "refuse_conversion " source:term " expect " expected:str : tactic => do
  let target ← Lean.Elab.Term.elabTerm source (some (mkSort .zero))
  Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let refused ← try
    let _ ← Hex.RCF.proveGoal target
    pure false
  catch error =>
    let message ← error.toMessageData.toString
    unless message.startsWith expected.getString do
      throwError "wrong conversion refusal: {message}"
    pure true
  unless refused do throwError "expected terminal conversion refusal"
  Lean.Elab.Tactic.closeMainGoal `refuse_conversion (mkConst ``True.intro)

example : True := by
  refuse_conversion (∀ x : ℝ,
    x ^ 2 + ((RealAlgebraicNumber.ofAlgebraic? (AlgebraicNumber.ofRat 1)).getD
      (0 / (CubeTwo.realAlgebraic - CubeTwo.realAlgebraic))).toReal > 0)
    expect "rcf: original closed divisor is zero"

example : True := by
  refuse_conversion (∀ x : ℝ,
    x ^ 2 + ((RealAlgebraicNumber.ofAlgebraic? CubeTwo.realAlgebraic.toAlgebraic).getD
      ((1 / 0 : ℚ) • CubeTwo.realAlgebraic)).toReal > 0)
    expect "rcf: original closed divisor is zero"

example : True := by
  refuse_conversion (∀ x : ℝ,
    x ^ 2 + ((RealAlgebraicNumber.ofAlgebraic? CubeTwo.realAlgebraic.toAlgebraic).getD
      (CubeTwo.realAlgebraic / (CubeTwo.realAlgebraic - CubeTwo.realAlgebraic))).toReal > 0)
    expect "rcf: original closed divisor is zero"

example : True := by
  refuse_conversion (∀ x : ℝ,
    x ^ 2 + ((RealAlgebraicNumber.ofAlgebraic? CubeTwo.realAlgebraic.toAlgebraic).getD
      (Coefficients.ofField CubeTwo.realAlgebraic
        (CubeTwo.realAlgebraic.toAlgebraic.toQAdjoin / 0))).toReal > 0)
    expect "rcf: original closed divisor is zero"

run_meta do
  let sources : Array Q(Prop) := #[
    q(∀ x : ℝ,
      x ^ 2 + ((RealAlgebraicNumber.ofAlgebraic? CubeTwo.realAlgebraic.toAlgebraic).getD
        ((CubeTwo.realAlgebraic.toAlgebraic / 0).re)).toReal > 0),
    q(∀ x : ℝ,
      x ^ 2 + ((RealAlgebraicNumber.ofAlgebraic? CubeTwo.realAlgebraic.toAlgebraic).getD
        ((CubeTwo.realAlgebraic - CubeTwo.realAlgebraic) ^ (-1 : ℤ))).toReal > 0),
    q(∀ x : ℝ,
      x ^ 2 + ((RealAlgebraicNumber.ofAlgebraic? CubeTwo.realAlgebraic.toAlgebraic).getD
        (RealAlgebraicNumber.intPow CubeTwo.realAlgebraic (-1))).toReal > 0),
    q(∀ x : ℝ,
      x ^ 2 + ((RealAlgebraicNumber.ofAlgebraic? CubeTwo.realAlgebraic.toAlgebraic).getD
        ((AlgebraicNumber.inv CubeTwo.realAlgebraic.toAlgebraic).re)).toReal > 0),
    q(∀ x : ℝ,
      x ^ 2 + ((RealAlgebraicNumber.ofAlgebraic? CubeTwo.realAlgebraic.toAlgebraic).getD
        ((fun y : RealAlgebraicNumber => y / y) CubeTwo.realAlgebraic)).toReal > 0)]
  for source in sources do
    let .error (.unsupported _ _) ← Reify.prepare source |
      throwError "unsupported discarded-branch arithmetic was admitted"

example : True := by
  refuse_conversion (∀ x : ℝ,
    x ^ 2 + ((RealAlgebraicNumber.ofAlgebraic? CubeTwo.realAlgebraic.toAlgebraic).getD
      (RealAlgebraicNumber.ofRat (0 / (1 - 1)))).toReal > 0)
    expect "rcf: original closed divisor is zero"

example : True := by
  refuse_conversion (∀ x : ℝ,
    x ^ 2 + ((RealAlgebraicNumber.ofAlgebraic? AlgebraicNumber.I).getD
      (RealAlgebraicNumber.ofRat (-1))).toReal > 0)
    expect "rcf: the universal sentence is false"

example : True := by
  refuse_conversion (∀ x : ℝ, x ^ 2 + 0 *
    ((CubeTwo.realAlgebraic - CubeTwo.realAlgebraic) /
      (CubeTwo.realAlgebraic - CubeTwo.realAlgebraic)).toReal > 0)
    expect "rcf: original closed divisor is zero"

example : True := by
  refuse_conversion (∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 0 → x ^ 2 +
    (RealAlgebraicNumber.ofRat 0 / RealAlgebraicNumber.ofRat 0).toReal > 0)
    expect "rcf: original closed divisor is zero"

example : True := by
  refuse_conversion (∀ x : ℝ,
    x + ((RealAlgebraicNumber.ofAlgebraic? AlgebraicNumber.I).getD
      CubeTwo.realAlgebraic).toReal = x)
    expect "rcf: the universal sentence is false"

-- Keep the full-query comparison mode covered alongside the default interval mode.
set_option rcf.algebraic.intervalSigns false in
theorem interval_quotation : ∃ x : ℝ, x ^ 2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 := by rcf

theorem default_quotation : ∃ x : ℝ, x ^ 2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 := by rcf

run_meta do
  let usesInterval ← ProofEvidence.contains ``interval_quotation fun e =>
    e.isAppOfArity ``LiteralSign.Entry.mk 4 &&
      e.getAppArgs[3]!.isAppOfArity ``Option.none 1
  unless !usesInterval do throwError "full-query control quoted interval evidence"
  unless ← ProofEvidence.contains ``interval_quotation (fun e =>
      e.isAppOfArity ``LiteralSign.Entry.mk 4 &&
        e.getAppArgs[3]!.isAppOfArity ``Option.some 2) do
    throwError "full-query control quoted no query entries"
  unless ← ProofEvidence.contains ``default_quotation (fun e =>
      e.isAppOfArity ``LiteralSign.Entry.mk 4 &&
        e.getAppArgs[3]!.isAppOfArity ``Option.none 1) do
    throwError "default quotation quoted no interval entries"

/-- info: 'Hex.RCF.CheckedConversions.rational_radicals' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rational_radicals
/-- info: 'Hex.RCF.CheckedConversions.default_quotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms default_quotation

/-- info: 'Hex.RCF.CheckedConversions.unused_algebraic_divisor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unused_algebraic_divisor
/-- info: 'Hex.RCF.CheckedConversions.converted_radical_divisor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms converted_radical_divisor

/-- info: 'Hex.RCF.CheckedConversions.selected_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selected_value
/-- info: 'Hex.RCF.CheckedConversions.rational_fallback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rational_fallback
/-- info: 'Hex.RCF.CheckedConversions.algebraic_fallback' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms algebraic_fallback
/-- info: 'Hex.RCF.CheckedConversions.nested_conversion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nested_conversion
/-- info: 'Hex.RCF.CheckedConversions.selected_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selected_projection
/-- info: 'Hex.RCF.CheckedConversions.imaginary_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms imaginary_projection
/-- info: 'Hex.RCF.CheckedConversions.original_divisor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms original_divisor
/-- info: 'Hex.RCF.CheckedConversions.algebraic_divisor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms algebraic_divisor
/-- info: 'Hex.RCF.CheckedConversions.radical_conversion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms radical_conversion
/-- info: 'Hex.RCF.CheckedConversions.checked_rational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checked_rational
/-- info: 'Hex.RCF.CheckedConversions.field_conversion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms field_conversion
/-- info: 'Hex.RCF.CheckedConversions.field_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms field_projection
/-- info: 'Hex.RCF.CheckedConversions.nonreal_projection' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms nonreal_projection
/-- info: 'Hex.RCF.CheckedConversions.computed_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms computed_power
/-- info: 'Hex.RCF.CheckedConversions.computed_product' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms computed_product
/-- info: 'Hex.RCF.CheckedConversions.computed_inverse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms computed_inverse
/-- info: 'Hex.RCF.CheckedConversions.computed_negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms computed_negative
/-- info: 'Hex.RCF.CheckedConversions.direct_division' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms direct_division
/-- info: 'Hex.RCF.CheckedConversions.integer_casts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms integer_casts
/-- info: 'Hex.RCF.CheckedConversions.direct_power' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms direct_power
/-- info: 'Hex.RCF.CheckedConversions.direct_radical_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms direct_radical_base

/-- info: 'Hex.RCF.CheckedConversions.coerced_radical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms coerced_radical

/-- info: 'Hex.RCF.CheckedConversions.coerced_divisor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms coerced_divisor

/-- info: 'Hex.RCF.CheckedConversions.field_divisor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms field_divisor

/-- info: 'Hex.RCF.CheckedConversions.reduced_quotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms reduced_quotation

end Hex.RCF.CheckedConversions

/-- info: 'Hex.RCF.CheckedConversions.interval_quotation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RCF.CheckedConversions.interval_quotation
