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

private meta def rejected (action : MetaM α) : MetaM Unit := do
  let count := (← getMCtx).decls.toList.length
  let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
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
  unless (← getMCtx).decls.toList.length == count &&
      (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
    throwError "recursive rejection retained caller state"

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
  let decode := ScalarQuote.decoderWith factsFor base
  let .ok quoted ← RootQuote.run original decode
    | throwError "recursive scalar quotation failed"
  unless quoted.usage.proofNodes == 14374 do
    throwError "recursive scalar accounting changed: {quoted.usage.proofNodes}"
  unless (← calls.get).size == 2 && quoted.usage.sourceNodes == 38 do
    throwError "recursive quotation did not visit both selected predecessors exactly once"
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
  let .error (.budget exhausted) ← RootQuote.run original decode (config (quoted.usage.proofNodes-1))
    | throwError "one-below recursive scalar budget did not exhaust"
  unless exhausted.dimension == .proofNodes && exhausted.consumed == 13449 &&
      exhausted.requested == 925 do
    throwError "recursive scalar exhaustion moved from the final925-node charge"
  logInfo m!"recursive exhausted: consumed={exhausted.consumed}, requested={exhausted.requested}"
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
  rejected (RootQuote.run original
    (ScalarQuote.decoderWith (fun _ => pure (some (mkConst ``Records.facts))) leaf))
  unless (← leafCalls.get) == 0 do throwError "wrong-context facts reached the leaf decoder"

theorem sign : restored.sign = -1 := by rfl

/-- info: -1 -/
#guard_msgs in
#eval restored.sign

end Hex.RCF.RecursiveScalarQuote
