/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public meta import HexRCF.RealCoefficients.RootHeader
public meta section

/-! Retain reconstructed descriptors and prepare their native contexts for
quotation without expanding anonymous descriptor expressions during replay. -/
namespace Hex.RCF.RealCoefficients.RootPrepare
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RealFormula.Reify

/-- The original constructed context and an equal retained context. The decoder
uses checked header equations; it supplies neither source authentication nor
an ordinary-real model. All declarations belong to the enclosing transaction. -/
structure Result where
  root : Expr
  rootEq : Expr
  source : Expr
  context : Expr
  same : Expr
  binding : Expr
  decoder : RootQuote.DecoderM
  usage : Hex.Reflect.BudgetUsage

private def closed (name : Name) (expression : Expr) : ReifyM Expr := do
  let expression ← instantiateMVars expression
  if expression.hasFVar || expression.hasMVar || expression.hasLooseBVars then
    throwError "rcf: root preparation requires closed retained inputs"
  accountProof expression
  let expression ← Hex.RCF.checkExpr name expression
  Meta.check expression
  return expression

private def checked (name : Name) (target candidate : Expr) : ReifyM Expr := do
  accountProof target
  accountProof candidate
  Hex.RCF.checkProof name target candidate

/-- These are monomorphic quotation data, not compiled producer proposals. -/
private def retain (name : Name) (expression : Expr) : ReifyM (Expr × Expr) := do
  let expression ← closed name expression
  let kind ← inferType expression
  if expression.hasLevelParam || kind.hasLevelParam then
    throwError "rcf: retained root data must be monomorphic"
  accountProof kind
  let declaration := mkPrivateName (← getEnv) (← mkFreshUserName name)
  let retained ← mkAuxDefinition declaration kind expression (compile := false)
  let target ← mkEq expression retained
  let candidate := mkExpectedPropHint (← mkEqRefl expression) target
  return (retained,← checked `RootPrepare.retained target candidate)

private def decoderWith (context binding rootBinding : Expr) (config : Simp.Config) :
    ReifyM RootQuote.DecoderM := do
  let context ← closed `RootPrepare.context context
  let binding ← closed `RootPrepare.binding binding
  let rootBinding ← closed `RootPrepare.rootBinding rootBinding
  let kind ← inferType binding
  unless kind.isAppOfArity ``Eq 3 do throwError "rcf: root header binding is not an equation"
  let lhs := kind.getAppArgs[1]!
  unless lhs.getAppFn.isConstOf ``Descriptor.raw do
    throwError "rcf: root header binding has a different subject"
  let root := lhs.getAppArgs.back!
  let target ← mkEq (← mkAppM ``Algebraic.Context.root #[context]) root
  let rootBinding ← checked `RootPrepare.rootBinding target rootBinding
  let binding ← checked `RootPrepare.binding kind binding
  let mut laws : SimpTheorems := {}
  laws ← laws.add (.stx `rootBinding Syntax.missing) #[] rootBinding (post := false)
  laws ← laws.add (.stx `rawBinding Syntax.missing) #[] binding (post := false)
  let simpContext ← Simp.mkContext config #[laws]
  return fun expression => do
    charge .proofNodes 1
    if expression.hasLooseBVars || expression.hasMVar then return none
    unless (← withTransparency .reducible <| whnf (← inferType expression)).isConstOf ``Bool do
      return none
    let (result,work) ← Meta.simpCore expression simpContext
    charge .proofNodes work.numSteps
    if result.expr == expression then return none
    let target ← mkEq expression result.expr
    return some (← checked `RootPrepare.rewrite target (← result.getProof' expression))

/-- Construct the native `Context.adjoin` at the reconstructed descriptor and
retain an equal context whose descriptor has a private checked definition.
Both descriptor/raw and context/root equations are checked at their exact
subjects before use. The supplied cleanliness function remains unchanged.

Compose `same` with the original reader through `ScalarPacket.quoteWith`.
Run preparation and subsequent quotation in one `RootQuote.runWith` request:
input checks, retained definitions, equations, simplifier visits and resulting
proofs share its budget. The simplifier limit is separately caller-configurable;
its exceptions are terminal. Failure rolls back the caller's complete state.
This is quotation preparation, not frozen history or coefficient support. -/
def prepareWith (header : RootHeader.Result) (clean : Expr)
    (config : Simp.Config := {maxSteps := 100000}) : ReifyM Result := do
  let clean ← closed `RootPrepare.clean clean
  let raw ← closed `RootPrepare.raw header.raw
  let rawBinding ← closed `RootPrepare.rawBinding header.binding
  let (root,rootEq) ← retain `RootPrepare.root header.root.value
  let target ← mkEq (← mkAppM ``Descriptor.raw #[root]) raw
  let binding ← checked `RootPrepare.raw target (mkExpectedPropHint rawBinding target)
  let source ← mkAppM ``Algebraic.Context.adjoin #[header.root.value,clean]
  let native ← mkAppM ``Algebraic.Context.adjoin #[root,clean]
  let (context,_) ← retain `RootPrepare.context native
  let target ← mkEq source context
  let same ← checked `RootPrepare.same target (mkExpectedPropHint (← mkEqRefl source) target)
  let rootBinding ← mkAppM ``Algebraic.Context.root_adjoin #[root,clean]
  let decoder ← decoderWith context binding rootBinding config
  return ⟨root,rootEq,source,context,same,binding,decoder,(← get).budget.consumed⟩

end Hex.RCF.RealCoefficients.RootPrepare
