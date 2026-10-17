/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.SharedQuoteCases
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests
namespace Hex.RCF.SharedQuoteCallbacks
open CellReplayTests.Algebraic Hex.RealFormula.Reify
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

def coordinate : DensePoly Data.parent.Value := DensePoly.C ScalarQuoteTests.restored

theorem coordinate_sign : Upper.context.signPoly coordinate = -1 :=
  (Algebraic.Context.signPoly_const Upper.context coordinate (DensePoly.size_C_le_one _)).trans
    ((congrArg Data.parent.sign (DensePoly.coeff_C ScalarQuoteTests.restored 0)).trans
      ScalarQuoteTests.restored_sign)

def facts : List (Algebraic.SignFact Upper.context) := [⟨coordinate,-1,coordinate_sign⟩]
def elementLiteral : Codec.Json := .array (.cons
  (.array (.cons ScalarQuoteTests.literal .nil)) (.cons (.number (-1)) .nil))
def literal : Codec.Json := .array (.cons elementLiteral .nil)
def reader := Codec.readPoly
  (Algebraic.Element.codec (context := Upper.context)
    (Algebraic.Element.codec (context := Data.native) Data.base.codec)) literal

def hiddenReader := Codec.readPoly
  (Algebraic.Element.signCodec (context := Upper.context)
    (Algebraic.Element.codec (context := Data.native) Data.base.codec) facts) literal

theorem predecessor_read :
    (Algebraic.Element.codec (context := Data.native) Data.base.codec).decode
      ScalarQuoteTests.literal = .ok ScalarQuoteTests.restored :=
  RootQuote.read_eq _ _ ScalarQuoteTests.canonical_read

def wrongSecond : Codec.Json := .array
  (.cons ScalarQuoteTests.literal (.cons ScalarQuoteTests.wrongSign .nil))
def trailingZero : Codec.Json := .array
  (.cons ScalarQuoteTests.literal (.cons (.array .nil) .nil))

private meta def observeTerminal (action : MetaM α) (handler : Exception → MetaM α) : MetaM α :=
  fun metaContext metaState coreContext coreState => do
    try action metaContext metaState coreContext coreState
    catch error => handler error metaContext metaState coreContext coreState

private meta def rejected (action : MetaM α) : MetaM Unit := do
  let failed ← observeTerminal (action *> pure false) fun error => do
    if error.isMaxHeartbeat || error.isMaxRecDepth then throw error
    match error with
    | .error _ _ => pure true
    | _ => throw error
  unless failed do throwError "invalid quotation shape was accepted"

private meta def emit (name : Name) (reader : Expr) (result : RootQuote.Result) : MetaM Unit := do
  let statement ← mkEq (← mkAppM ``Except.toOption #[reader])
    (← mkAppM ``Option.some #[result.value])
  let proof ← Hex.RCF.checkProof `quotationSource statement result.proof
  withExporting (isExporting := true) do
    addDecl (.thmDecl {name,levelParams := [],type := statement,value := proof})

private meta def config (limit : Nat) : Hex.RealFormula.Reify.Config :=
  {ring := {budget := {Hex.Reflect.Budget.default with proofNodes := limit}}}

private meta def unchanged (action : MetaM Unit) : MetaM Unit := do
  let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let count := (← getMCtx).decls.toList.length
  action
  unless (← (← getEnv).getLocalConstantInfos).map (·.name) == names &&
      (← getMCtx).decls.toList.length == count do
    throwError "polynomial rejection retained declarations or metavariables"

run_meta do
  withExporting (isExporting := false) do
    let accepted ← getConstInfo ``predecessor_read
    let subject := accepted.type.getAppArgs[1]!
    let calls ← IO.mkRef (0 : Nat)
    let completed ← IO.mkRef (0 : Nat)
    let decode : RootQuote.DecoderM := fun expression => do
      if let .proj ``ValueCodec 1 codec := expression.getAppFn then
        if codec.getAppFn.isConstOf ``Algebraic.Element.codec &&
            expression.getAppNumArgs == 1 then
          let context := codec.getAppArgs[codec.getAppNumArgs-2]!
          if ← withNewMCtxDepth <| withTransparency .reducible
              (isDefEq context (mkConst ``Data.native)) then
            calls.modify (·+1)
            charge .sourceNodes 17
            let result ← ScalarQuote.quoteDecodeWith expression (mkConst ``Records.facts)
              (fun e => liftM (RationalQuote.decoder (mkConst ``Data.registry) e))
            completed.modify (·+1)
            return some (← mkAppM ``RootQuote.read_eq #[expression,result.value,result.proof])
      liftM (RationalQuote.decoder (mkConst ``Data.registry) expression)
    let some original ← unfoldDefinition? (mkConst ``reader)
      | throwError "nested polynomial reader unavailable"
    let .ok quoted ← RootQuote.runWith
        (ScalarQuote.quotePolyWith original (mkConst ``facts) decode)
      | throwError "nested predecessor polynomial quotation failed"
    unless quoted.usage.proofNodes == 9141 do
      throwError "nested transport proof-node accounting changed: {quoted.usage.proofNodes}"
    let count ← calls.get
    unless count == 1 && (← completed.get) == 1 && quoted.usage.sourceNodes == 17 do
      throwError "polynomial did not invoke and charge its actual predecessor callback"
    withExporting (isExporting := true) do
      let statement ← mkEq (← mkAppM ``Except.toOption #[mkConst ``reader])
        (← mkAppM ``Option.some #[quoted.value])
      addDecl (.thmDecl {
        name := `Hex.RCF.SharedQuoteCallbacks.read_checked,levelParams := [],
        type := statement,value := ← Hex.RCF.checkProof `nestedPolynomial statement quoted.proof})
    let .ok exact ← RootQuote.runWith
        (ScalarQuote.quotePolyWith original (mkConst ``facts) decode) (config quoted.usage.proofNodes)
      | throwError "exact nested projection budget failed"
    unless exact.usage.proofNodes == quoted.usage.proofNodes do
      throwError "nested projection quotation changed its usage"
    unchanged do
      let .error (.budget exhausted) ← RootQuote.runWith
          (ScalarQuote.quotePolyWith original (mkConst ``facts) decode)
          (config (quoted.usage.proofNodes-1))
        | throwError "one-below nested projection budget did not exhaust"
      unless exhausted.dimension == .proofNodes do throwError "wrong nested budget dimension"
      unless exhausted.consumed == 8135 && exhausted.requested == 1006 do
        throwError "nested final transport charge changed: consumed={exhausted.consumed}, requested={exhausted.requested}"
      logInfo m!"nested exhausted: consumed={exhausted.consumed}, requested={exhausted.requested}"
    let codec := match subject.getAppFn with
      | .proj ``ValueCodec 1 codec => codec
      | _ => subject.getAppArgs[1]!
    let codecType ← inferType codec
    let constant := mkApp3 (mkConst ``ValueCodec.decode) codecType.appArg! codec
      (mkConst ``ScalarQuoteTests.literal)
    let .ok direct ← RootQuote.runWith (ScalarQuote.quoteDecodeWith constant (mkConst ``Records.facts)
        (fun e => liftM (RationalQuote.decoder (mkConst ``Data.registry) e)))
      | throwError "constant projection decode helper failed"
    emit `Hex.RCF.SharedQuoteCallbacks.constant_read constant direct
    for bad in #[mkNatLit 7,mkAppN constant.getAppFn (constant.getAppArgs.extract 0 2)] do
      unchanged do
        rejected (RootQuote.runWith (ScalarQuote.quoteDecodeWith bad (mkConst ``Records.facts)))
    calls.set 0
    completed.set 0
    unchanged do
      let .error (.providerFailure (.invalidProviderEvidence ⟨key,version⟩ _) _) ←
          RootQuote.run (mkConst ``hiddenReader) decode
        | throwError "hidden original codec did not return its structured boundary rejection"
      unless key == `Hex.RCF.RealCoefficients.RootQuote.boundary && version == 0 do
        throwError "hidden codec failed at a different boundary"
    unless (← completed.get) > 0 do throwError "hidden-codec rejection did not follow callback completion"
    calls.set 0
    completed.set 0
    let .ok bare ← RootQuote.run subject decode
      | throwError "protected canonical decode did not reach its callback"
    emit `Hex.RCF.SharedQuoteCallbacks.bare_read subject bare
    unless (← calls.get) > 0 && bare.usage.sourceNodes == (← calls.get)*17 do
      throwError "bare protected decoder did not charge its accepted proposal"
    unchanged do
      rejected (RootQuote.run subject)
    let some flat ← unfoldDefinition? (mkConst ``SharedQuoteTests.reader)
      | throwError "flat polynomial reader unavailable"
    for bad in #[mkConst ``wrongSecond,mkConst ``trailingZero] do
      let badReader := mkAppN flat.getAppFn (flat.getAppArgs.set! 4 bad)
      unchanged do
        let .error (.providerFailure (.invalidProviderEvidence ..) _) ← RootQuote.runWith
            (ScalarQuote.quotePolyWith badReader (mkConst ``Records.facts) decode)
          | throwError "noncanonical polynomial or wrong second sign was accepted"
    for bad in #[mkAppN flat.getAppFn (flat.getAppArgs.extract 0 4),mkConst ``SharedQuoteTests.reader] do
      unchanged do
        rejected (RootQuote.runWith (ScalarQuote.quotePolyWith bad (mkConst ``Records.facts) decode))
    calls.set 0
    let terminal : RootQuote.DecoderM := fun _ => do
      calls.modify (·+1)
      let _ ← mkFreshExprMVar (mkConst ``Nat)
      abort (.providerDeclined (.unsupportedCarrier (mkConst ``Nat)) Hex.Reflect.Budget.zero #[])
    unchanged do
      let .error (.providerDeclined (.unsupportedCarrier _) _ _) ← RootQuote.run subject terminal
        | throwError "structured provider decline was retried or changed"
    unless (← calls.get) == 1 do throwError "structured provider decline called a fallback"
    logInfo m!"nested polynomial predecessor callbacks={count}; sourceNodes={quoted.usage.sourceNodes}; proofNodes={quoted.usage.proofNodes}"
    logInfo "protected codec, wrong second sign, trailing zero and malformed heads checked with rollback"
end Hex.RCF.SharedQuoteCallbacks
