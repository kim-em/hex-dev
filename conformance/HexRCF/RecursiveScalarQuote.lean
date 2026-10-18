/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.SharedQuoteCallbacks
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests Hex.RealFormula.Reify
namespace Hex.RCF.RecursiveScalarQuote
open CellReplayTests.Algebraic
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

/-- Keep the exact predecessor codec visible to the quotation transaction. -/
def reader (codec : ValueCodec (Algebraic.Element Upper.context)) :=
  codec.decode SharedQuoteCallbacks.elementLiteral

private meta def config (limit : Nat) : Hex.RealFormula.Reify.Config :=
  {ring := {budget := {Hex.Reflect.Budget.default with proofNodes := limit}}}

private meta def unchanged (action : MetaM Unit) : MetaM Unit := do
  let count := (← getMCtx).decls.toList.length
  let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
  action
  unless (← getMCtx).decls.toList.length == count &&
      (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
    throwError "recursive rejection retained caller state"

private meta def rejected (action : MetaM α) : MetaM Unit := unchanged do
  let failed ← (fun context state coreContext coreState => do
    try
      let _ ← action context state coreContext coreState
      pure false
    catch error =>
      if error.isMaxHeartbeat || error.isMaxRecDepth then throw error
      match error with
      | .error _ _ => pure true
      | _ => throw error : MetaM Bool)
  unless failed do throwError "missing or mismatched recursive facts were accepted"

private meta def emit (name : Name) (reader : Expr) (result : RootQuote.Result) : MetaM Unit := do
  let statement ← mkEq (← mkAppM ``Except.toOption #[reader])
    (← mkAppM ``Option.some #[mkConst `Hex.RCF.RecursiveScalarQuote.restored])
  let proof ← Hex.RCF.checkProof `recursiveReader statement result.proof
  addDecl (.thmDecl {name,levelParams := [],type := statement,value := proof})

run_meta do
  let some template ← unfoldDefinition? (mkConst ``SharedQuoteCallbacks.reader)
    | throwError "recursive scalar source unavailable"
  let original := mkApp (mkConst ``reader) template.getAppArgs[3]!
  let calls ← IO.mkRef (#[] : Array Expr)
  let factsFor : Expr → ReifyM (Option Expr) := fun codec => do
    charge .sourceNodes 19
    calls.modify (·.push codec)
    let context := codec.getAppArgs[codec.getAppNumArgs-2]!
    if ← withNewMCtxDepth <| withTransparency .reducible
        (isDefEq context (mkConst ``Upper.context)) then
      return some (mkConst ``SharedQuoteCallbacks.facts)
    if ← withNewMCtxDepth <| withTransparency .reducible
        (isDefEq context (mkConst ``Data.native)) then
      return some (mkConst ``Records.facts)
    return none
  let base : RootQuote.DecoderM := fun expression =>
    liftM (RationalQuote.decoder (mkConst ``Data.registry) expression)
  let sentinel ← mkFreshExprMVar (mkConst ``Nat)
  let mutated ← IO.mkRef false
  let mutateFacts : Expr → ReifyM (Option Expr) := fun codec => do
    unless ← sentinel.mvarId!.isAssigned do sentinel.mvarId!.assign (mkNatLit 1)
    mutated.set true
    factsFor codec
  let decode := ScalarQuote.decoderWith mutateFacts base
  let .ok quoted ← RootQuote.run original decode
    | throwError "recursive scalar quotation failed"
  unless (← mutated.get) && !(← sentinel.mvarId!.isAssigned) do
    throwError "successful recursive quotation did not restore the mutated caller"
  unless quoted.usage.proofNodes == 30316 do
    throwError "recursive scalar accounting changed: {quoted.usage.proofNodes}"
  unless (← calls.get).size == 2 && quoted.usage.sourceNodes == 38 do
    throwError "recursive quotation did not visit both selected predecessors exactly once"
  for (codec,expected) in (← calls.get).zip #[mkConst ``Upper.context,mkConst ``Data.native] do
    let context := codec.getAppArgs[codec.getAppNumArgs-2]!
    unless ← withNewMCtxDepth <| withTransparency .reducible (isDefEq context expected) do
      throwError "recursive quotation visited a different context or order"
  logInfo m!"recursive scalar proofNodes={quoted.usage.proofNodes}; lookups=2; sourceNodes=38"
  let declaration := Declaration.defnDecl {
    name := `Hex.RCF.RecursiveScalarQuote.restored,levelParams := [],
    type := ← inferType quoted.value,value := quoted.value,hints := .regular 0,safety := .safe}
  addDecl declaration (forceExpose := true)
  compileDecl declaration (logErrors := true)
  let statement ← mkEq (← mkAppM ``Except.toOption #[original])
    (← mkAppM ``Option.some #[mkConst `Hex.RCF.RecursiveScalarQuote.restored])
  let proof ← Hex.RCF.checkProof `recursiveReader statement quoted.proof
  addDecl (.thmDecl {
    name := `Hex.RCF.RecursiveScalarQuote.read_checked,levelParams := [],type := statement,value := proof})
  let .ok exact ← RootQuote.run original decode (config quoted.usage.proofNodes)
    | throwError "exact recursive scalar budget failed"
  unless exact.usage == quoted.usage do throwError "exact recursive usage changed"
  mutated.set false
  unchanged do
    let .error (.budget exhausted) ← RootQuote.run original decode (config (quoted.usage.proofNodes-1))
      | throwError "one-below recursive scalar budget did not exhaust"
    unless exhausted.dimension == .proofNodes && exhausted.consumed == 29391 &&
        exhausted.requested == 925 do
      throwError "recursive scalar final charge changed: {exhausted.consumed}+{exhausted.requested}"
    logInfo m!"recursive exhausted: consumed={exhausted.consumed}, requested={exhausted.requested}"
  unless (← mutated.get) && !(← sentinel.mvarId!.isAssigned) do
    throwError "exhausted recursive quotation did not restore the mutated caller"
  calls.set #[]
  let constant := mkApp3 (mkConst ``ValueCodec.decode) (← inferType quoted.value)
    original.appArg! (mkConst ``SharedQuoteCallbacks.elementLiteral)
  let constantCalls ← IO.mkRef (0 : Nat)
  let .ok constantResult ← RootQuote.run constant (fun expression => do
      let proposed ← decode expression
      if expression == constant then constantCalls.modify (·+1)
      if expression == constant && proposed.isNone then
        throwError "recursive factory declined its constant-form probe"
      return proposed)
    | throwError "recursive constant-form decode failed"
  unless (← constantCalls.get) == 1 && (← calls.get).size == 2 &&
      constantResult.usage.proofNodes == 28294 do
    throwError "recursive constant-form branch changed: nodes={constantResult.usage.proofNodes}; calls={← constantCalls.get}; lookups={(← calls.get).size}"
  let constantStatement ← mkEq (← mkAppM ``Except.toOption #[constant])
    (← mkAppM ``Option.some #[mkConst `Hex.RCF.RecursiveScalarQuote.restored])
  let constantProof ← Hex.RCF.checkProof `recursiveConstant constantStatement constantResult.proof
  addDecl (.thmDecl {
    name := `Hex.RCF.RecursiveScalarQuote.constant_read,levelParams := [],
    type := constantStatement,value := constantProof})
  calls.set #[]
  let tagged := mkMData (KVMap.empty.setNat `rcfQuotation 2) constant
  let taggedCalls ← IO.mkRef (0 : Nat)
  let .ok taggedResult ← RootQuote.run tagged (fun expression => do
      let proposed ← decode expression
      if expression == tagged then taggedCalls.modify (·+1)
      if expression == tagged && proposed.isNone then
        throwError "recursive factory declined its annotated probe"
      return proposed)
    | throwError "annotated recursive scalar decode failed"
  unless (← taggedCalls.get) == 1 && (← calls.get).size == 2 &&
      taggedResult.usage.proofNodes == 28307 do
    throwError "annotated recursive scalar branch changed: nodes={taggedResult.usage.proofNodes}; calls={← taggedCalls.get}; lookups={(← calls.get).size}"
  emit `Hex.RCF.RecursiveScalarQuote.tagged_read tagged taggedResult
  calls.set #[]
  let retries ← IO.mkRef (0 : Nat)
  let retryFacts : Expr → ReifyM (Option Expr) := fun codec => do
    let facts ← factsFor codec
    let context := codec.getAppArgs[codec.getAppNumArgs-2]!
    if ← withNewMCtxDepth <| withTransparency .reducible
        (isDefEq context (mkConst ``Data.native)) then
      retries.modify (·+1)
      if (← retries.get) == 1 then return none
    return facts
  let .ok retryResult ← RootQuote.run original (ScalarQuote.decoderWith retryFacts base)
    | throwError "recursive scalar retry did not accept"
  unless (← retries.get) == 2 && (← calls.get).size == 3 &&
      retryResult.usage.sourceNodes == 57 && retryResult.usage.proofNodes == 31022 do
    throwError "recursive scalar retry changed: nodes={retryResult.usage.proofNodes}; retries={← retries.get}; lookups={(← calls.get).size}; source={retryResult.usage.sourceNodes}"
  logInfo m!"recursive variants: constant={constantResult.usage.proofNodes}; tagged={taggedResult.usage.proofNodes}; retry={retryResult.usage.proofNodes}"
  emit `Hex.RCF.RecursiveScalarQuote.retry_read original retryResult
  let leafCalls ← IO.mkRef (0 : Nat)
  let leaf : RootQuote.DecoderM := fun expression => do
    let scalar := expression.getAppFn.isConstOf ``ValueCodec.decode ||
      match expression.getAppFn with
      | .proj ``ValueCodec 1 _ => true
      | _ => false
    if scalar then leafCalls.modify (·+1)
    pure none
  rejected (RootQuote.run original (ScalarQuote.decoderWith (fun _ => pure none) leaf))
  unless (← leafCalls.get) == 0 do throwError "missing selected facts tried another decoder"
  leafCalls.set 0
  rejected (RootQuote.run original
    (ScalarQuote.decoderWith (fun _ => pure (some (mkConst ``Records.facts))) leaf))
  unless (← leafCalls.get) == 0 do throwError "wrong-context facts reached the leaf decoder"
  for wrong in [false,true] do
    calls.set #[]
    leafCalls.set 0
    let refused ← IO.mkRef false
    mutated.set false
    let inner : Expr → ReifyM (Option Expr) := fun codec => do
      calls.modify (·.push codec)
      let context := codec.getAppArgs[codec.getAppNumArgs-2]!
      if ← withNewMCtxDepth <| withTransparency .reducible
          (isDefEq context (mkConst ``Upper.context)) then
        return some (mkConst ``SharedQuoteCallbacks.facts)
      unless ← withNewMCtxDepth <| withTransparency .reducible
          (isDefEq context (mkConst ``Data.native)) do
        throwError "unexpected recursive refusal context"
      refused.set true
      if wrong then
        sentinel.mvarId!.assign (mkNatLit 1)
        mutated.set true
        let _ ← mkFreshExprMVar (mkConst ``Nat)
        return some (mkConst ``SharedQuoteCallbacks.facts)
      return none
    let afterRefusal : RootQuote.DecoderM := fun expression => do
      if ← refused.get then leaf expression else pure none
    rejected (RootQuote.run original (ScalarQuote.decoderWith inner afterRefusal))
    let visited ← calls.get
    unless visited.size == (if wrong then 2 else 3) && (← leafCalls.get) == 0 &&
        (← refused.get) && (← mutated.get) == wrong && !(← sentinel.mvarId!.isAssigned) do
      throwError "inner refusal: wrong={wrong}; visits={visited.size}; leaf={(← leafCalls.get)}; assigned={(← sentinel.mvarId!.isAssigned)}"
    logInfo m!"recursive inner refusal: wrong={wrong}; lookups={visited.size}; rollback checked"

theorem sign : restored.sign = -1 := by
  unfold restored
  exact Algebraic.Element.restore_sign _ _ _ _

/-- info: -1 -/
#guard_msgs in
#eval restored.sign

end Hex.RCF.RecursiveScalarQuote
