/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RowQuoteData
public meta import HexRCF.RealCoefficients.RowQuote
public section
namespace Hex.RCF.RowQuoteTests
open Lean Meta Hex.RealFormula.Reify Hex.RCF.RealCoefficients
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
private meta def reader (input : Expr) (expected : Int) : MetaM Expr := do
  let rootEq ← mkAppM ``Input.rootEq #[input]
  let q1 ← mkAppM ``Input.q1 #[input]
  let queries ← mkListLit (← inferType q1) [q1]
  let row ← mkAppM ``castRow #[input]
  let some row ← unfoldDefinition? row | throwError "cast fixture did not expose its transport"
  let retarget ← mkAppM ``RowOperations.retarget
    #[mkConst ``Int.sign,toExpr (),rootEq,← mkEqRefl queries,row]
  let value ← mkAppM ``Hex.SignDet.SelectedSigns.value #[retarget]
  let decision ← mkDecide (← mkEq value (toExpr expected))
  mkAppM ``gate #[decision]
private meta def restored (before : MetavarContext) (sentinel : Expr)
    (names : Option (Array Name) := none) : MetaM Unit := do
  let after ← getMCtx
  unless !(← sentinel.mvarId!.isAssigned) && before.mvarCounter == after.mvarCounter &&
      before.lmvarCounter == after.lmvarCounter && before.eAssignment.toList == after.eAssignment.toList &&
      before.lAssignment.toList == after.lAssignment.toList &&
      before.decls.toList.map Prod.fst == after.decls.toList.map Prod.fst do
    throwError "projection quotation retained caller metavariables"
  if let some names := names then
    unless (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
      throwError "failed projection quotation retained declarations"
run_meta do
  for (stored,expected,result,name) in #[(1,1,17,`projectPositive),(1,0,23,`projectFalse),
      (-1,0,23,`projectNegative),(0,0,17,`projectZero)] do
    withLocalDeclD `input (mkApp (mkConst ``Input) (toExpr (stored : Int))) fun input => do
      let subject ← reader input expected
      let .ok quoted ← RootQuote.run subject RowQuote.decoder
        | throwError "projection quotation refused its ordinary control"
      let target ← mkEq (← mkAppM ``Except.toOption #[subject])
        (← mkAppM ``Option.some #[mkNatLit result])
      let checked ← Hex.RCF.checkProof name target (mkExpectedPropHint quoted.proof target)
      let target ← mkForallFVars #[input] target
      let proof ← mkLambdaFVars #[input] checked
      let fullName := Name.append `Hex.RCF.RowQuoteTests name
      addDecl (.thmDecl {name := fullName,levelParams := [],type := target,value := proof})
      logInfo m!"{name}: proofNodes={quoted.usage.proofNodes}"
run_meta do
  withLocalDeclD `input (mkApp (mkConst ``Input) (toExpr (1 : Int))) fun input => do
    let subject ← reader input 1
    let sentinel ← mkFreshExprMVar (mkConst ``Nat)
    let before ← getMCtx
    let action : ReifyM RootQuote.Result := do
      sentinel.mvarId!.assign (mkNatLit 41)
      RootQuote.quoteWith subject RowQuote.decoder
    let .ok result ← RootQuote.runWith action
      | throwError "projection quotation baseline refused"
    restored before sentinel
    unless result.usage.proofNodes == 2622 do
      throwError "projection quotation budget changed: {result.usage.proofNodes}"
    let basic : Hex.RealFormula.Reify.Config := {}
    let exactConfig := {basic with ring := {basic.ring with budget :=
      {basic.ring.budget with proofNodes := result.usage.proofNodes}}}
    let .ok exactResult ← RootQuote.runWith action exactConfig
      | throwError "projection quotation rejected exact budget"
    unless exactResult.usage == result.usage do throwError "projection quotation accounting changed"
    restored before sentinel
    let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
    let small := {exactConfig with ring := {exactConfig.ring with budget :=
      {exactConfig.ring.budget with proofNodes := result.usage.proofNodes-1}}}
    let .error (.budget exhausted) ← RootQuote.runWith action small
      | throwError "projection quotation accepted below budget"
    unless exhausted.dimension == .proofNodes do throwError "projection exhausted the wrong resource"
    restored before sentinel (some names)
    logInfo m!"projection exact/below budget and caller rollback checked; exact={result.usage.proofNodes}"
    let invalid : ReifyM RootQuote.Result := do
      sentinel.mvarId!.assign (mkNatLit 43)
      RootQuote.quoteWith subject (fun expression => do
        let some _ ← RowQuote.decoder expression | return none
        return some (← mkEqRefl (mkConst ``Bool.false)))
    let rejected ← try
        let _ ← RootQuote.runWith invalid
        pure false
      catch _ => pure true
    unless rejected do throwError "projection callback accepted a proof of the wrong Boolean goal"
    restored before sentinel (some names)
    logInfo "wrong-goal callback rejection and caller rollback checked"
end Hex.RCF.RowQuoteTests
