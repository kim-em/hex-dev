/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RootQuoteData
public import HexSignDet.Conformance
public meta import HexRCF.RealCoefficients.RootQuote
public section
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.RootQuoteTests
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192

private meta def scalarProof? (expression : Expr) : MetaM (Option Expr) := do
  if let .proj ``ValueCodec 1 _ := expression.getAppFn then
    if expression.getAppNumArgs == 1 then
      for n in ([-3,0,1,-8,8,3] : List Int) do
        let proof ← mkAppM ``decode_integer #[toExpr n]
        let type ← inferType proof
        if ← withTransparency .all <| withNewMCtxDepth
            (isDefEq expression type.getAppArgs[1]!) then
          return some proof
  return none

-- The statement is well typed, but the supplied proof proves reflexivity.
-- Its expected-type hint defeats a Meta-only type-agreement check.
private meta def forgedProof (expression : Expr) : MetaM Expr := do
  let resultType ← whnf (← inferType expression)
  let rejected ← mkAppOptM ``Except.error #[some resultType.getAppArgs[0]!,
    some resultType.getAppArgs[1]!,some (mkStrLit "forged rejection")]
  let statement ← mkEq expression rejected
  let _ ← Hex.RCF.checkProof `wellTypedFalseEquation (← mkEq statement statement)
    (← mkEqRefl statement)
  return mkExpectedPropHint (← mkEqRefl expression) statement

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

/-- A recursor returning a function has an extra argument without a Boolean
reflection proof. Its major remains blocked until the public table law applies. -/
@[expose] noncomputable def functionReader : Except String Nat :=
  Nat.rec (motive := fun _ => Nat → Except String Nat)
    (fun value => .ok value) (fun _ previous value => previous (value+1))
    (((Replay.leaf Hex.SignDet.Conformance.literalNode).table
      Hex.SignDet.Conformance.literal_accepts).count []) 5

run_meta do
  withExporting (isExporting := false) do
    let .ok result ← RootQuote.quote (mkConst ``functionReader)
      | throwError "non-Boolean recursor reader declined"
    let someSeven ← mkAppM ``Option.some #[mkNatLit 7]
    let statement ← mkEq (← mkAppM ``Except.toOption #[mkConst ``functionReader]) someSeven
    withExporting (isExporting := true) do
      addDecl (.thmDecl {
        name := `Hex.RCF.RootQuoteTests.function_read,levelParams := [],
        type := statement,value := mkExpectedPropHint result.proof statement })

/-- A Boolean recursor's fifth argument can be an ordinary function input. -/
@[expose] noncomputable def boolFunctionReader : Except String Nat :=
  cond (Node.check Sturm.orderSign 7 Hex.Sturm.Fixtures.p (.finite (-2)) (.finite 2)
    [] Hex.SignDet.Conformance.literalNode)
    (fun value => .ok (value+2)) (fun _ => .error "false branch") 5

/-- A dependent conditional can itself return a function. -/
@[expose] noncomputable def dependentFunctionReader : Except String Nat :=
  (if _accepted : Node.check Sturm.orderSign 7 Hex.Sturm.Fixtures.p
      (.finite (-2)) (.finite 2) [] Hex.SignDet.Conformance.literalNode = true then
    fun value => .ok (value+2)
  else fun _ => .error "false dependent branch") 5

run_meta do
  withExporting (isExporting := false) do
    for (reader,name) in #[(``boolFunctionReader,`Hex.RCF.RootQuoteTests.boolFunction_read),
        (``dependentFunctionReader,`Hex.RCF.RootQuoteTests.dependentFunction_read)] do
      let .ok result ← RootQuote.quote (mkConst reader)
        | throwError "function-valued Boolean reader declined"
      let someSeven ← mkAppM ``Option.some #[mkNatLit 7]
      let statement ← mkEq (← mkAppM ``Except.toOption #[mkConst reader]) someSeven
      withExporting (isExporting := true) do
        addDecl (.thmDecl {
          name,levelParams := [],type := statement,
          value := mkExpectedPropHint result.proof statement})

/-- Acceptance is used as dependent returned data, exercising the true branch. -/
@[expose] noncomputable def trueReader : Except String (PLift
    (Node.check Sturm.orderSign 7 Hex.Sturm.Fixtures.p (.finite (-2)) (.finite 2)
      [] Hex.SignDet.Conformance.literalNode = true)) :=
  if accepted : Node.check Sturm.orderSign 7 Hex.Sturm.Fixtures.p
      (.finite (-2)) (.finite 2) [] Hex.SignDet.Conformance.literalNode = true then
    .ok ⟨accepted⟩
  else .error "checked literal node rejected"

run_meta do
  withExporting (isExporting := false) do
    let .ok result ← RootQuote.quote (mkConst ``trueReader) scalarProof?
      | throwError "dependent true reader declined"
    withExporting (isExporting := true) do
      let name := `Hex.RCF.RootQuoteTests.trueValue
      addDecl (.defnDecl {
        name,levelParams := [],type := ← inferType result.value,value := result.value,
        hints := .regular 0,safety := .safe }) (forceExpose := true)
      let statement ← mkEq (← mkAppM ``Except.toOption #[mkConst ``trueReader])
        (← mkAppM ``Option.some #[mkConst name])
      addDecl (.thmDecl {
        name := `Hex.RCF.RootQuoteTests.true_read,levelParams := [],
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
    withoutModifyingEnv do
      let accepted ← IO.mkRef false
      let .ok _ ← RootQuote.quote reader (fun expression => do
        let proof ← scalarProof? expression
        if proof.isSome && !(← accepted.get) then
          mutate sentinel
          accepted.set true
        return proof)
        | throwError "accepted scalar callback failed"
      unless (← accepted.get) && !(← sentinel.mvarId!.isAssigned) &&
          (← getEnv).contains `Hex.RCF.RootQuoteTests.rollbackMarker do
        throwError "accepted callback effects did not follow success-state policy"
    for mode in [0,1,2,3,4] do
      unchanged do
        let reached ← IO.mkRef false
        let raised ← observeTerminal (do
          let _ ← withOptions (debug.skipKernelTC.set · true) do
            RootQuote.quote reader (fun expression => do
              let proof ← scalarProof? expression
              if let some good := proof then
                let proposed ← if mode == 0 then mkEqRefl (mkNatLit 0)
                  else if mode == 3 then forgedProof expression
                  else if mode == 4 then mkSorry (← inferType good) false
                  else pure good
                reached.set true
                mutate sentinel
                if mode == 1 then throwError "deliberate scalar callback failure"
                if mode == 2 then throwInterruptException
                return some proposed
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
    let .ok _ ← withOptions (debug.skipKernelTC.set · true) <|
        RootQuote.quote reader scalarProof?
      | throwError "quotation did not recover with caller kernel checking disabled"
    withExporting (isExporting := true) do
      let name := `Hex.RCF.RootQuoteTests.runFinished
      addDecl (.thmDecl {
        name,levelParams := [],type := mkConst ``True,value := mkConst ``True.intro})

end Hex.RCF.RootQuoteTests
