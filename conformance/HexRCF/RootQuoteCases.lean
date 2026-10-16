/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RootQuoteData
public meta import HexRCF.RealCoefficients.RootQuote
public section
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.RootQuoteTests
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192

private meta def scalarProof? (expression : Expr) : MetaM (Option Expr) := do
  if let .proj ``ValueCodec 1 codec := expression.getAppFn then
    if expression.getAppNumArgs == 1 then
      let payload ← withTransparency .all (whnf expression.appArg!)
      if let .proj ``ValueCodec 0 encodedCodec := payload.getAppFn then
        if payload.getAppNumArgs == 1 then
          let expected ← mkAppM ``Tower.Context.codec #[mkConst ``base]
          if ← withTransparency .all <| withNewMCtxDepth (isDefEq codec expected) then
            if ← withTransparency .all <| withNewMCtxDepth (isDefEq codec encodedCodec) then
              return some (← mkAppM ``decode_value #[payload.appArg!])
  return none

-- Observe underlying EIO without supplying rollback on behalf of the API.
private meta def observeTerminal (action : MetaM α) (handler : Exception → MetaM α) : MetaM α :=
  fun metaContext metaState coreContext coreState => do
    try action metaContext metaState coreContext coreState
    catch error => handler error metaContext metaState coreContext coreState

private meta def unchanged (action : MetaM Unit) : MetaM Unit := do
  let count := (← getMCtx).decls.toList.length
  let names ← (← getEnv).getLocalConstantInfos
  let names := names.map (·.name)
  let statuses ← #[``Node.check,``SignTable.count,``Array.mapM.map].mapM getReducibilityStatus
  action
  unless (← getMCtx).decls.toList.length == count do
    throwError "failed quotation retained metavariables"
  unless (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
    throwError "failed quotation retained declarations"
  unless (← #[``Node.check,``SignTable.count,``Array.mapM.map].mapM getReducibilityStatus) == statuses do
    throwError "failed quotation changed reducibility"

private meta def mutate (sentinel : Expr) : MetaM Unit := do
  let _ ← mkFreshExprMVar (mkConst ``Nat)
  sentinel.mvarId!.assign (mkNatLit 1)
  let name := `Hex.RCF.RootQuoteTests.rollbackMarker
  let type ← mkEq (mkNatLit 0) (mkNatLit 0)
  addDecl (.thmDecl {name,levelParams := [],type,value := ← mkEqRefl (mkNatLit 0)})

run_meta do
  withExporting (isExporting := false) do
    let names := #[``Node.check,``SignTable.count,``Array.mapM.map]
    let statuses ← names.mapM getReducibilityStatus
    let count := (← getMCtx).decls.toList.length
    let .ok result ← RootQuote.quote (mkConst ``read) scalarProof?
      | throwError "cubic literal quotation declined"
    unless (← getMCtx).decls.toList.length == count do
      throwError "literal quotation retained caller metavariables"
    unless (← names.mapM getReducibilityStatus) == statuses do
      throwError "literal quotation changed reducibility"
    logInfo m!"cubic literal quotation proof budget: {result.usage.proofNodes}"
    withExporting (isExporting := true) do
      let name := `Hex.RCF.RootQuoteTests.nativeRoot
      addDecl (.defnDecl {
        name,levelParams := [],type := ← inferType result.value,value := result.value,
        hints := .regular 0,safety := .safe }) (forceExpose := true)
      let statement ← mkEq (← mkAppM ``Except.toOption #[mkConst ``read])
        (← mkAppM ``Option.some #[mkConst name])
      addDecl (.thmDecl {
        name := `Hex.RCF.RootQuoteTests.nativeRoot_read,levelParams := [],
        type := statement,value := mkExpectedPropHint result.proof statement })

run_meta do
  withExporting (isExporting := false) do
    let reader := mkConst ``read
    let config : Hex.RealFormula.Reify.Config := {}
    let .ok control ← RootQuote.quote reader scalarProof?
      | throwError "healthy quotation control failed"
    let carried := {Hex.Reflect.Budget.zero with proofNodes := 11}
    let exactConfig := {config with ring := {config.ring with budget :=
      {config.ring.budget with proofNodes := control.usage.proofNodes + 11}}}
    let .ok exact ← RootQuote.quote reader scalarProof? exactConfig carried
      | throwError "quotation rejected the exact aggregate budget"
    unless exact.usage.proofNodes == control.usage.proofNodes + 11 do
      throwError "quotation reset prior proof usage"
    for limit in [0,control.usage.proofNodes-1] do
      unchanged do
        let limited := {config with ring := {config.ring with budget :=
          {config.ring.budget with proofNodes := limit}}}
        let .error (.budget exhausted) ← RootQuote.quote reader scalarProof? limited
          | throwError "quotation did not preserve proof-budget exhaustion"
        unless exhausted.dimension == .proofNodes do throwError "wrong exhausted dimension"
    let .ok _ ← RootQuote.quote (mkConst ``wrongNodeReader) scalarProof?
      | throwError "changed-count control is not syntactically valid node data"
    for rejected in [``wrongVersion,``wrongCount] do
      unchanged do
        let .error (.providerFailure (.invalidProviderEvidence _ _) _) ←
            RootQuote.quote (mkConst rejected) scalarProof?
          | throwError "malformed or false replay evidence was accepted"
    let sentinel ← mkFreshExprMVar (mkConst ``Nat)
    -- Even a callback declining an unrelated boundary must undo its mutations.
    let declined ← IO.mkRef false
    let .ok _ ← RootQuote.quote reader (fun expression => do
      let proof ← scalarProof? expression
      if proof.isNone && !(← declined.get) then
        declined.set true
        mutate sentinel
      return proof)
      | throwError "a declined scalar proposal changed successful replay"
    unless (← declined.get) && !(← sentinel.mvarId!.isAssigned) &&
        !(← getEnv).contains `Hex.RCF.RootQuoteTests.rollbackMarker do
      throwError "declined scalar proposal did not restore caller state"
    -- Reach a real scalar boundary before lying or raising an exception.
    for mode in [0,1,2] do
      unchanged do
        let reached ← IO.mkRef false
        let raised ← observeTerminal (do
          let _ ← RootQuote.quote reader (fun expression => do
            let proof ← scalarProof? expression
            if proof.isSome then
              reached.set true
              mutate sentinel
              if mode == 0 then return some (← mkEqRefl (mkNatLit 0))
              if mode == 1 then throwError "deliberate scalar callback failure"
              throwInterruptException
            return none)
          pure false) (fun error => do
            if mode == 2 then
              unless error.isInterrupt do throw error
            else
              match error with
              | .error _ _ => pure ()
              | _ => throw error
            pure true)
        unless raised && (← reached.get) && !(← sentinel.mvarId!.isAssigned) do
          throwError "invalid scalar proposal or callback failure was swallowed"
    let token ← IO.CancelToken.new
    token.set
    let resources : List (String × (Core.Context → Core.Context) × (Exception → Bool)) := [
      ("heartbeat",fun context => {context with maxHeartbeats := 1,initHeartbeats := 0},Exception.isMaxHeartbeat),
      ("recursion",fun context => {context with maxRecDepth := 8,currRecDepth := 0},Exception.isMaxRecDepth),
      ("interruption",fun context => {context with cancelTk? := some token},Exception.isInterrupt)]
    for (label,limits,expected) in resources do
      unchanged do
        let terminal ← observeTerminal
          (withTheReader Core.Context limits do
            let _ ← RootQuote.quote reader scalarProof?
            pure false)
          (fun error => do
            unless expected error do throw error
            pure true)
        unless terminal do throwError "literal quotation swallowed {label}"
    unchanged do
      let failed ← observeTerminal (do
        let _ ← RootQuote.quote (mkNatLit 0)
        pure false) (fun error => do
          match error with
          | .error _ _ => pure true
          | _ => throw error)
      unless failed do throwError "quotation accepted a non-reader"
    let .ok _ ← RootQuote.quote reader scalarProof?
      | throwError "quotation did not recover after terminal failures"
    withExporting (isExporting := true) do
      let name := `Hex.RCF.RootQuoteTests.runFinished
      addDecl (.thmDecl {
        name,levelParams := [],type := mkConst ``True,value := mkConst ``True.intro})

end Hex.RCF.RootQuoteTests
