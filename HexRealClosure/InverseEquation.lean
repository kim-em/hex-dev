/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.InversePacking

public section

namespace Hex.RealClosure.Algebraic.Packing
open Hex.SignDet

variable {E : Type u} {Ctx : Type v} [Zero E] [DecidableEq E]
variable [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
variable [DecidableEq Ctx] {coeffSign : E → Int} {parent : Ctx}
variable {context : Context E Ctx coeffSign parent}

namespace Inverse

/-- A supplied output is an inverse at the retained selected root. This
certificate binds the actual operand and checked product-minus-one equation;
it does not assert equality with the native gcd algorithm's literal candidate. -/
structure Equation (entry : Packing context) where
  private mk ::
  argument : Element context
  nonzero : argument.sign ≠ 0
  signs : SelectedSigns context.root
    [argument.polynomial, argument.polynomial * entry.value.polynomial - 1]
  observed : signs.values.toList = [argument.sign, 0]

/-- Validate the supplied output's same-root inverse equation. Only the
operand's cached nonzero tag and the checked joint signs are tested; no inverse
candidate, gcd, extended gcd, splitting, isolation or query producer runs. -/
def Equation.make? (argument : Element context) (entry : Packing context)
    (signs : SelectedSigns context.root
      [argument.polynomial, argument.polynomial * entry.value.polynomial - 1]) :
    Option (Inverse.Equation entry) :=
  if nonzero : argument.sign ≠ 0 then
    if observed : signs.values.toList = [argument.sign, 0] then
      some ⟨argument, nonzero, signs, observed⟩
    else none
  else none

/-- Successful validation retains the requested operand literally. -/
theorem Equation.make?_argument (argument : Element context) (entry : Packing context)
    (signs : SelectedSigns context.root
      [argument.polynomial, argument.polynomial * entry.value.polynomial - 1])
    {record : Inverse.Equation entry}
    (accepted : Inverse.Equation.make? argument entry signs = some record) :
    record.argument = argument := by
  unfold Inverse.Equation.make? at accepted
  split at accepted
  · split at accepted
    · cases Option.some.inj accepted
      rfl
    · cases accepted
  · cases accepted

/-- Rechecking the retained equation returns the same full certificate. -/
theorem Equation.make?_self {entry : Packing context} (record : Inverse.Equation entry) :
    Inverse.Equation.make? record.argument entry record.signs = some record := by
  cases record
  rename_i argument nonzero signs observed
  simp [Inverse.Equation.make?, nonzero, observed]

/-- Read the supplied inverse equation from an already checked graph memo.
The existing selected-sign reader binds the original operand, output, root
domain and query positions. Native candidate computation is absent. -/
def Equation.readMemo? (argument : Element context) (entry : Packing context)
    {head : DensePoly E} {lower upper : Hex.Endpoint E}
    (memo : Array (Dag.Checked coeffSign parent head lower upper))
    (index : Nat) : Option (Inverse.Equation entry) := do
  let signs ← SelectedSigns.readMemo? context.root
    [argument.polynomial, argument.polynomial * entry.value.polynomial - 1]
    ⟨#[argument.sign, 0], rfl⟩ memo index
  Inverse.Equation.make? argument entry signs

/-- Reading an equation retains the original operand, including its stored
polynomial and cached tag. -/
theorem Equation.readMemo?_argument (argument : Element context) (entry : Packing context)
    {head : DensePoly E} {lower upper : Hex.Endpoint E}
    (memo : Array (Dag.Checked coeffSign parent head lower upper)) (index : Nat)
    {record : Inverse.Equation entry}
    (accepted : Inverse.Equation.readMemo? argument entry memo index = some record) :
    record.argument = argument := by
  unfold Inverse.Equation.readMemo? at accepted
  cases selected : SelectedSigns.readMemo? context.root
      [argument.polynomial, argument.polynomial * entry.value.polynomial - 1]
      ⟨#[argument.sign, 0], rfl⟩ memo index with
  | none => simp [selected] at accepted
  | some signs =>
    simp only [selected, bind, Option.bind] at accepted
    exact Inverse.Equation.make?_argument argument entry signs accepted

/-- An exact native inverse record already supplies the same-root equation. -/
def toEquation {entry : Packing context} (record : Inverse entry) :
    Inverse.Equation entry :=
  ⟨record.argument, record.nonzero, record.signs, record.observed⟩

/-- Conversion retains the exact native operand without exposing its factory. -/
@[simp] theorem toEquation_argument {entry : Packing context} (record : Inverse entry) :
    record.toEquation.argument = record.argument := by
  unfold toEquation
  rfl

/-- Conversion retains the literal checked replay, independently of its query
indexing, without exposing either private constructor. -/
@[simp] theorem toEquation_evidence {entry : Packing context} (record : Inverse entry) :
    record.toEquation.signs.evidence = record.signs.evidence := by
  unfold toEquation
  rfl

end Inverse

end Hex.RealClosure.Algebraic.Packing

/-- info: 'Hex.RealClosure.Algebraic.Packing.Inverse.Equation.make?_argument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.Inverse.Equation.make?_argument

/-- info: 'Hex.RealClosure.Algebraic.Packing.Inverse.Equation.make?_self' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.Inverse.Equation.make?_self

/-- info: 'Hex.RealClosure.Algebraic.Packing.Inverse.Equation.readMemo?_argument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.Inverse.Equation.readMemo?_argument

/-- info: 'Hex.RealClosure.Algebraic.Packing.Inverse.toEquation_argument' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.Inverse.toEquation_argument

/-- info: 'Hex.RealClosure.Algebraic.Packing.Inverse.toEquation_evidence' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Algebraic.Packing.Inverse.toEquation_evidence
