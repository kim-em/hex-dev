/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.TreeQuoteData
public meta import HexRCF.RealCoefficients.RootQuote
public section
open Lean Meta Hex.RCF.RealCoefficients
namespace Hex.RCF.TreeQuote
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768

run_meta do
  for (reader,result,name) in #[(``leafTrue,7,`Hex.RCF.TreeQuote.leafAccepted),
      (``leafFalse,29,`Hex.RCF.TreeQuote.leafRefused),
      (``splitTrue,31,`Hex.RCF.TreeQuote.splitAccepted),
      (``splitFalse,37,`Hex.RCF.TreeQuote.splitRefused)] do
    let .ok quoted ← RootQuote.quote (mkConst reader)
      | throwError "public replay equation quotation refused {reader}"
    let target ← mkEq (← mkAppM ``Except.toOption #[mkConst reader])
      (← mkAppM ``Option.some #[mkNatLit result])
    let proof ← Hex.RCF.checkProof name target (mkExpectedPropHint quoted.proof target)
    addDecl (.thmDecl {name,levelParams := [],type := target,value := proof})
    logInfo m!"{reader}: proofNodes={quoted.usage.proofNodes}"
private meta def restored (before : MetavarContext) (sentinel : Expr)
    (names : Option (Array Name) := none) : MetaM Unit := do
  let after ← getMCtx
  unless !(← sentinel.mvarId!.isAssigned) && before.mvarCounter == after.mvarCounter &&
      before.lmvarCounter == after.lmvarCounter && before.eAssignment.toList == after.eAssignment.toList &&
      before.lAssignment.toList == after.lAssignment.toList &&
      before.decls.toList.map Prod.fst == after.decls.toList.map Prod.fst do
    throwError "replay quotation retained caller metavariables"
  if let some names := names then
    unless (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
      throwError "failed replay quotation retained declarations"
run_meta do
  let sentinel ← mkFreshExprMVar (mkConst ``Nat)
  let before ← getMCtx
  let action : Hex.RealFormula.Reify.ReifyM RootQuote.Result := do
    sentinel.mvarId!.assign (mkNatLit 41)
    RootQuote.quoteWith (mkConst ``leafTrue)
  let .ok result ← RootQuote.runWith action
    | throwError "leaf quotation baseline refused"
  unless result.usage.proofNodes == 101056 do
    throwError "leaf quotation budget changed: {result.usage.proofNodes}"
  restored before sentinel
  let basic : Hex.RealFormula.Reify.Config := {}
  let exactConfig := {basic with ring := {basic.ring with budget :=
    {basic.ring.budget with proofNodes := result.usage.proofNodes}}}
  let .ok exactResult ← RootQuote.runWith action exactConfig
    | throwError "leaf quotation rejected exact budget"
  unless exactResult.usage == result.usage do throwError "leaf quotation accounting changed"
  restored before sentinel
  let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let small := {exactConfig with ring := {exactConfig.ring with budget :=
    {exactConfig.ring.budget with proofNodes := result.usage.proofNodes-1}}}
  let .error (.budget exhausted) ← RootQuote.runWith action small
    | throwError "leaf quotation accepted below budget"
  unless exhausted.dimension == .proofNodes do throwError "leaf quotation exhausted wrong resource"
  restored before sentinel (some names)
  logInfo "public replay leaf exact/below budget and caller rollback checked"
run_meta do
  let sentinel ← mkFreshExprMVar (mkConst ``Nat)
  let before ← getMCtx
  let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
  for rejected in [``wrongContext,``swappedChildren] do
    let .error (.providerFailure (.invalidProviderEvidence _ _) _) ← RootQuote.runWith (do
        sentinel.mvarId!.assign (mkNatLit 43)
        RootQuote.quoteWith (mkConst rejected))
      | throwError "quotation accepted a rejected replay reader"
    restored before sentinel (some names)
  logInfo "wrong-context/swapped-child reader failures and caller rollback checked"

end Hex.RCF.TreeQuote
