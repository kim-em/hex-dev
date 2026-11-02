/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RootPreparePacket
public meta import HexRCF.RootPreparePacket
public meta import HexRCF.RealCoefficients.RootPrepare
public meta import HexRCF.RealCoefficients.RationalQuote
public section

/-! Exact request budgets and rollback after retained-context preparation and replay. -/
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.RootPrepareControls
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

private meta def restored (before : MetavarContext) (sentinel : Expr)
    (declarations : Option (Array Name) := none) : MetaM Unit := do
  let after ← getMCtx
  unless !(← sentinel.mvarId!.isAssigned) && before.mvarCounter == after.mvarCounter &&
      before.lmvarCounter == after.lmvarCounter &&
      before.eAssignment.toList == after.eAssignment.toList &&
      before.lAssignment.toList == after.lAssignment.toList &&
      before.decls.toList.map Prod.fst == after.decls.toList.map Prod.fst do
    throwError "retained context quotation changed caller metavariables"
  if let some declarations := declarations then
    unless (← (← getEnv).getLocalConstantInfos).map (·.name) == declarations do
      throwError "failed retained context quotation kept auxiliary declarations"

run_meta do
  withoutExporting do
    let sentinel ← mkFreshExprMVar (mkConst ``Nat)
    let before ← getMCtx
    let action : Hex.RealFormula.Reify.ReifyM RootQuote.Result := do
      sentinel.mvarId!.assign (mkNatLit 37)
      RootPreparePacket.quoteWith 1
    let .ok result ← RootQuote.runWith action RootPreparePacket.config
      | throwError "retained packet baseline failed"
    restored before sentinel
    let exactConfig := {RootPreparePacket.config with ring :=
      {RootPreparePacket.config.ring with budget :=
        {RootPreparePacket.config.ring.budget with proofNodes := result.usage.proofNodes}}}
    let .ok repeated ← RootQuote.runWith action exactConfig
      | throwError "retained packet failed at its exact request budget"
    unless repeated.usage == result.usage do throwError "retained packet accounting changed"
    restored before sentinel
    let declarations := (← (← getEnv).getLocalConstantInfos).map (·.name)
    let small := {exactConfig with ring := {exactConfig.ring with budget :=
      {exactConfig.ring.budget with proofNodes := result.usage.proofNodes-1}}}
    let .error (.budget exhausted) ← RootQuote.runWith action small
      | throwError "retained packet accepted one node below its exact request budget"
    unless exhausted.dimension == .proofNodes do throwError "retained packet exhausted another dimension"
    restored before sentinel (some declarations)
    logInfo m!"retained packet exact/one-below request budget={result.usage.proofNodes}; caller state restored"

run_meta do
  withoutExporting do
    let sentinel ← mkFreshExprMVar (mkConst ``Nat)
    let before ← getMCtx
    let declarations := (← (← getEnv).getLocalConstantInfos).map (·.name)
    let .error (.providerFailure (.invalidProviderEvidence _ _) _) ← RootQuote.runWith (do
        sentinel.mvarId!.assign (mkNatLit 41)
        RootPreparePacket.quoteWith (-1)) RootPreparePacket.config
      | throwError "retained packet did not reject a wrong proposed sign"
    restored before sentinel (some declarations)
    logInfo "retained packet wrong-sign rejection restored caller declarations and metavariables"

run_meta do
  withoutExporting do
    for variant in [:3] do
      let sentinel ← mkFreshExprMVar (mkConst ``Nat)
      let before ← getMCtx
      let declarations := (← (← getEnv).getLocalConstantInfos).map (·.name)
      let reached ← IO.mkRef false
      let outcome ← try
        let result ← RootQuote.runWith (do
          sentinel.mvarId!.assign (mkNatLit 43)
          let some reader ← unfoldDefinition? (mkConst ``RootQuoteTests.read)
            | throwError "original descriptor reader is not exposed"
          let base : RootQuote.DecoderM := fun expression =>
            liftM (RationalQuote.decoder (mkConst ``RootQuoteTests.registry) expression)
          let header ← RootHeader.quoteWith reader base
          let clean ← mkAppM ``Tower.Context.isClean #[mkConst ``RootQuoteTests.base]
          reached.set true
          if variant == 0 then
            let unresolved ← mkFreshExprMVar (← inferType clean)
            discard <| RootPrepare.prepareWith header unresolved
          else if variant == 1 then
            let wrong ← mkEqRefl (mkNatLit 0)
            discard <| RootPrepare.prepareWith {header with binding := wrong} clean
          else
            let unresolved ← mkFreshExprMVar (← inferType header.raw)
            discard <| RootPrepare.prepareWith {header with raw := unresolved} clean
          return header.root) RootPreparePacket.config
        pure (some result)
      catch error =>
        if error.isInterrupt || error.isMaxHeartbeat || error.isMaxRecDepth then throw error
        pure none
      unless (← reached.get) do throwError "malformed-input control did not reach preparation"
      unless outcome.isNone do throwError "malformed retained input was not refused by preparation"
      restored before sentinel (some declarations)
      logInfo m!"malformed retained input refused with caller rollback: variant={variant}"

end Hex.RCF.RootPrepareControls
