/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RootQuoteData
public meta import HexRCF.RealCoefficients.RootHeader
public meta import HexRCF.RealCoefficients.RationalQuote
public section

/-! Budget and caller-state regressions for complete original root/header readers. -/
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.RootHeaderBudget
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
run_meta do
  withoutExporting do
    let decode : RootQuote.DecoderM := fun expression =>
      liftM (RationalQuote.decoder (mkConst ``RootQuoteTests.registry) expression)
    let some original ← unfoldDefinition? (mkConst ``RootQuoteTests.read)
      | throwError "root reader is not exposed"
    let .ok quoted ← RootQuote.runWith do
        let result ← RootHeader.quoteWith original decode
        unless result.root.usage == (← get).budget.consumed do
          throwError "header result omitted source parsing or binding charges"
        return result.root
      | throwError "generic header quotation declined"
    let config : Hex.RealFormula.Reify.Config := {}
    let exactConfig := {config with ring := {config.ring with budget :=
      {config.ring.budget with proofNodes := quoted.usage.proofNodes}}}
    let .ok exactResult ← RootQuote.runWith (do
        let result ← RootHeader.quoteWith original decode
        return result.root) exactConfig
      | throwError "header exact-budget quotation declined"
    unless exactResult.usage.proofNodes == quoted.usage.proofNodes do
      throwError "generic header resource accounting changed"
    let small := {config with ring := {config.ring with budget :=
      {config.ring.budget with proofNodes := quoted.usage.proofNodes-1}}}
    let .error (.budget exhausted) ← RootQuote.runWith (do
        let result ← RootHeader.quoteWith original decode
        return result.root) small
      | throwError "header quotation did not exhaust one node below budget"
    unless exhausted.dimension == .proofNodes do
      throwError "header quotation exhausted a different resource"
    logInfo m!"generic header exact/one-below budgets checked; nodes={quoted.usage.proofNodes}"
    let malformed := mkAppN original.getAppFn (original.getAppArgs.pop)
    let refused ← try
      let _ ← RootQuote.runWith do
        let result ← RootHeader.quoteWith malformed decode
        return result.root
      pure false
    catch error =>
      if error.isInterrupt || error.isMaxHeartbeat || error.isMaxRecDepth then throw error
      unless (← error.toMessageData.toString).contains "signatures differ" do throw error
      pure true
    unless refused do throwError "header accepted a partial descriptor reader"
    for source in [``RootQuoteTests.wrongVersion,``RootQuoteTests.wrongCount] do
      let some reader ← unfoldDefinition? (mkConst source)
        | throwError "negative reader is not exposed"
      let sentinel ← mkFreshExprMVar (mkConst ``Nat)
      let before ← getMCtx
      let visits ← IO.mkRef (0 : Nat)
      let declarations := (← (← getEnv).getLocalConstantInfos).map (·.name)
      let .error (.providerFailure (.invalidProviderEvidence _ _) _) ← RootQuote.runWith do
          let result ← RootHeader.quoteWith reader fun expression => do
            visits.modify (·+1)
            if !(← sentinel.mvarId!.isAssigned) then sentinel.mvarId!.assign (mkNatLit 9)
            decode expression
          return result.root
        | throwError "invalid original header reader did not reject"
      if source == ``RootQuoteTests.wrongCount && (← visits.get) == 0 then
        throwError "invalid count did not exercise callback state restoration"
      let after ← getMCtx
      unless !(← sentinel.mvarId!.isAssigned) && before.mvarCounter == after.mvarCounter &&
          before.lmvarCounter == after.lmvarCounter &&
          before.eAssignment.toList == after.eAssignment.toList &&
          before.lAssignment.toList == after.lAssignment.toList &&
          before.decls.toList.map Prod.fst == after.decls.toList.map Prod.fst &&
          (← (← getEnv).getLocalConstantInfos).map (·.name) == declarations do
        throwError "invalid header reader retained caller state"
      logInfo m!"generic header rejection and caller restoration checked: {source}"

end Hex.RCF.RootHeaderBudget
