/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.ScalarPacket
public import HexRCF.RealCoefficients.RootQuote
public meta import HexRCF.RealCoefficients.RootQuote
public meta section

namespace Hex.RCF.RealCoefficients.ScalarPacket
open Lean Meta Hex.RealFormula.Reify

/-- Quote one supplied sign packet through an equal prepared context, then
restore its fact in the original context. The exact original reader's model,
codec, literal and instance arguments are retained. Context equality is
ordinary checked evidence, not a source reconstruction procedure. All stages
share the enclosing reflection budget; the caller supplies `RootQuote.runWith`
for state restoration. Predecessor decoding and arithmetic retain their supplied
implementation; this does not establish strict compiled replay on deeper parents. -/
def quoteWith (reader prepared same : Expr)
    (decode : RootQuote.DecoderM := fun _ => pure none) : ReifyM RootQuote.Result := do
  let reader ← instantiateMVars reader
  let prepared ← instantiateMVars prepared
  let same ← instantiateMVars same
  accountProof reader
  accountProof prepared
  accountProof same
  let inspected := reader.consumeMData
  let head := inspected.getAppFn.consumeMData
  unless head.isConstOf ``read do
    throwError "rcf: expected a supplied ScalarPacket.read application"
  let declaration ← getConstInfo ``read
  let parameters := declaration.type.getNumHeadForalls
  unless inspected.getAppNumArgs == parameters && parameters ≥ 6 &&
      head.constLevels!.length == declaration.levelParams.length do
    throwError "rcf: expected a complete ScalarPacket.read application"
  for name in #[``restore,``read_restore] do
    let info ← getConstInfo name
    unless info.type.getNumHeadForalls == parameters+1 &&
        info.levelParams.length == declaration.levelParams.length do
      throwError "rcf: scalar packet restoration signature changed"
  let reader ← Hex.RCF.checkExpr `ScalarPacket.reader reader
  Meta.check reader
  let args := inspected.getAppArgs
  let index ← forallTelescope declaration.type fun binders _ => do
    for index in [:binders.size] do
      let binder ← getFVarLocalDecl binders[index]!
      if binder.userName == `context then
        unless binder.type.getAppFn.isConstOf ``Hex.RealClosure.Algebraic.Context do
          throwError "rcf: scalar packet context binder has changed type"
        return index
    throwError "rcf: scalar packet context binder is missing"
  let context := args[index]!
  let sameType ← mkEq context prepared
  let same ← Hex.RCF.checkProof `ScalarPacket.context sameType same
  let frozen := mkAppN inspected.getAppFn (args.set! index prepared)
  let quoted ← RootQuote.quoteOptionWith frozen decode
  let motive ← withLocalDeclD `context (← inferType context) fun context => do
    let atContext := mkAppN inspected.getAppFn (args.set! index context)
    mkLambdaFVars #[context] (← mkAppM ``Option.isSome #[atContext])
  accountProof motive
  let transport ← mkAppM ``congrArg #[motive,same]
  let type ← whnf (← inferType frozen)
  let isSome ← mkAppOptM ``Option.isSome #[some type.appArg!]
  let accepted ← mkEqTrans transport (← mkAppM ``congrArg #[isSome,quoted.proof])
  let statement ← mkEq (← mkAppM ``Option.isSome #[reader]) (mkConst ``Bool.true)
  accountProof accepted
  let accepted ← Hex.RCF.checkProof `ScalarPacket.accepted statement accepted
  let value := mkAppN (mkConst ``restore head.constLevels!) (args.push accepted)
  let proof := mkAppN (mkConst ``read_restore head.constLevels!) (args.push accepted)
  let statement ← mkEq reader (← mkAppM ``Option.some #[value])
  accountProof value
  accountProof proof
  let proof ← Hex.RCF.checkProof `ScalarPacket.restored statement proof
  return {value,proof,usage := (← get).budget.consumed}

end Hex.RCF.RealCoefficients.ScalarPacket
