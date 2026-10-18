/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.SourceIdentity
public meta import HexRCF.RealCoefficients.ScalarPacketQuote
public meta section

namespace Hex.RCF.RealCoefficients.SourceIdentity
open Lean Meta Hex Hex.RealClosure Hex.RealFormula.Reify

/-- Original source selection, including its checked isolating square and the
identity of that selected root with the original real expression. -/
structure Anchor where
  polynomial : Expr
  square : Expr
  witness : Expr
  precision : Expr
  value : Expr
  selected : Expr

/-- Two complete scalar readers at the same selected context. The value laws
bind their polynomial keys to the original equation and square margin. -/
structure Packets where
  equation : Expr
  enclosure : Expr
  equationValue : Expr
  enclosureValue : Expr

structure Result where
  root : Expr
  equation : Expr
  enclosure : Expr
  proof : Expr
  usage : Hex.Reflect.BudgetUsage

private def input (expression : Expr) : ReifyM Expr := do
  let expression ← instantiateMVars expression
  unless !expression.hasFVar && !expression.hasMVar && !expression.hasLooseBVars do
    throwError "rcf: selected source quotation requires closed inputs"
  accountProof expression
  Hex.RCF.checkExpr `SourceIdentity.input expression

private def arguments (name : Name) (expression : Expr) : ReifyM (Array Expr) := do
  let expression := expression.consumeMData
  unless expression.getAppFn.isConstOf name &&
      expression.getAppNumArgs == (← getConstInfo name).type.getNumHeadForalls do
    throwError "rcf: selected source quotation expected a complete {name} application"
  let args := expression.getAppArgs
  charge .proofNodes (args.size+1)
  let info ← getFunInfoNArgs expression.getAppFn args.size
  return args.zipIdx |>.filterMap fun (arg,i) =>
    if info.paramInfo[i]!.binderInfo.isExplicit then some arg else none

private def descriptor (context : Expr) : ReifyM Expr := do
  let mut context := context.consumeMData
  while !context.getAppFn.isConstOf ``Algebraic.Context.adjoin do
    Core.checkSystem "selected source context"
    charge .proofNodes 1
    let some next ← unfoldDefinition? context
      | throwError "rcf: selected source quotation requires an adjunction context"
    if next == context then throwError "rcf: selected source context did not unfold"
    accountProof next
    context := next.consumeMData
  let args ← arguments ``Algebraic.Context.adjoin context
  unless args.size == 2 do throwError "rcf: adjunction context signature changed"
  return args[0]!

private def signProof (fact : Expr) (sign : Int) : ReifyM Expr := do
  let target ← mkEq (← mkAppM ``Algebraic.SignFact.sign #[fact]) (toExpr sign)
  let candidate ← mkEqRefl (toExpr sign)
  accountProof target
  accountProof candidate
  Hex.RCF.checkProof `SourceIdentity.sign target (mkExpectedPropHint candidate target)

/-- Independently quote equation and enclosure packets, then authenticate the
original source at their same selected root. Both packets use the supplied
prepared-context equality. Their actual keys, signs and semantic value laws
are checked before composing the source identity. No producer or source search
runs here. Use the enclosing `RootQuote.runWith` transaction for rollback;
all inputs, readers and proofs consume that request's reflection budget. -/
def quoteWith (anchor : Anchor) (packets : Packets) (prepared same : Expr)
    (decode : RootQuote.DecoderM := fun _ => pure none) : ReifyM Result := do
  let polynomial ← input anchor.polynomial
  let square ← input anchor.square
  let witness ← input anchor.witness
  let precision ← input anchor.precision
  let value ← input anchor.value
  let selected ← input anchor.selected
  let equationReader ← input packets.equation
  let enclosureReader ← input packets.enclosure
  let equationValue ← input packets.equationValue
  let enclosureValue ← input packets.enclosureValue
  let prepared ← input prepared
  let same ← input same
  let inputs ← arguments ``ScalarPacket.read equationReader
  unless inputs.size == 6 do throwError "rcf: scalar source reader signature changed"
  let root ← descriptor inputs[2]!
  let equation ← ScalarPacket.quoteWith equationReader prepared same decode
  let enclosure ← ScalarPacket.quoteWith enclosureReader prepared same decode
  let zero ← signProof equation.value 0
  let positive ← signProof enclosure.value 1
  let model := inputs[0]!
  let fields ← #[``Tower.Model.value,``Tower.Model.zero_iff,``Tower.Model.one,
    ``Tower.Model.add,``Tower.Model.sub,``Tower.Model.mul,``Tower.Model.nat,
    ``Tower.Model.sign].mapM fun name => mkAppM name #[model]
  let actual ← mkAppM ``Hex.SignDet.Descriptor.root (fields.push root)
  let target ← mkEq actual value
  let candidate ← mkAppM ``identify #[model,root,polynomial,square,witness,precision,
    value,selected,equation.value,enclosure.value,equationValue,enclosureValue,zero,positive]
  accountProof target
  accountProof candidate
  let proof ← Hex.RCF.checkProof `SourceIdentity.selected target candidate
  return ⟨root,equation.value,enclosure.value,proof,(← get).budget.consumed⟩
end Hex.RCF.RealCoefficients.SourceIdentity
