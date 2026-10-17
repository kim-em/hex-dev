/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerContext
public meta import HexRCF.RealCoefficients.RootQuote

public meta section

/-! Checked native context assembly retaining the actual predecessor and descriptor. -/
namespace Hex.RCF.RealCoefficients.RootContext
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RealFormula.Reify

/-- A checked native context retaining the actual parent chain and descriptor.
The frame is the owner's serialization expression; freezing it is separate. -/
structure Result where
  context : Expr
  chain : Expr
  frame : Expr
  encoded : Expr
  checked : Expr
  binding : Expr
  usage : Hex.Reflect.BudgetUsage

private def closed (expression : Expr) : ReifyM Expr := do
  let expression ← instantiateMVars expression
  if expression.hasFVar || expression.hasMVar || expression.hasLooseBVars then
    throwError "rcf: root context packing requires closed retained inputs"
  let expression ← Hex.RCF.checkExpr `RootContext.input expression
  Meta.check expression
  return expression

/-- Assemble the owner's native root constructor from a closed retained parent
and a checked descriptor of its exact indexed type. The frame retains
`rootData parent.codec descriptor`; the identity conversion `Literal.ofJson`
checks its encoding without freezing or evaluating that serialization.
No arithmetic is reimplemented and no ring instance is added to stored values.
Use the enclosing `RootQuote.runWith` transaction for restoration and budgets.
Source-alias authentication and frozen origin/history assembly remain separate. -/
def packWith (parent descriptor : Expr) : ReifyM Result := do
  Core.checkSystem "native root context packing"
  accountProof parent
  accountProof descriptor
  let parent ← closed parent
  let descriptor ← closed descriptor
  let packed ← withTransparency .all (whnf parent)
  unless packed.getAppFn.isConstOf ``Tower.Context.pack do
    throwError "rcf: root packing requires an actual retained parent chain"
  let chain := packed.getAppArgs.back!
  let codec ← mkAppM ``Tower.Context.codec #[parent]
  let frame ← mkAppM ``Tower.rootData #[codec,descriptor]
  accountProof frame
  let statement ← mkEq (← mkAppM ``Tower.Literal.ofJson #[frame])
    (← mkAppM ``Option.some #[frame])
  let candidate := mkExpectedPropHint (← mkEqRefl (← mkAppM ``Option.some #[frame])) statement
  accountProof statement
  accountProof candidate
  let encoded ← Hex.RCF.checkProof `RootContext.frame statement candidate
  let next ← mkAppM ``Tower.Chain.root #[chain,descriptor,frame,encoded]
  let context ← closed (← mkAppM ``Tower.Context.pack #[next])
  accountProof context
  let statement ← mkEq context context
  let candidate ← mkEqRefl context
  accountProof statement
  accountProof candidate
  let checked ← Hex.RCF.checkProof `RootContext.checked statement candidate
  let signature ← mkAppM ``Tower.Context.signature #[context]
  let expected ← mkAppM ``Tower.Signature.extend
    #[← mkAppM ``Tower.Context.signature #[parent],frame]
  let statement ← mkEq signature expected
  let candidate := mkExpectedPropHint (← mkEqRefl expected) statement
  accountProof statement
  accountProof candidate
  let binding ← Hex.RCF.checkProof `RootContext.binding statement candidate
  return ⟨context,chain,frame,encoded,checked,binding,(← get).budget.consumed⟩

end Hex.RCF.RealCoefficients.RootContext
