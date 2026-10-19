/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RootHeaderValues
public meta import HexRCF.RealCoefficients.RootContext
public meta import HexRCF.RealCoefficients.RealModel
public section

/-! Native child contexts and ordinary-real interpretation of reconstructed roots. -/

open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.RootContextCases
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

run_meta do
  withoutExporting do
    let seen ← IO.mkRef (none : Option RootContext.Result)
    let action : Hex.RealFormula.Reify.ReifyM RootQuote.Result := do
      let result ← RootContext.packWith (mkConst ``RootQuoteTests.base)
        (mkConst ``RootHeaderPacket.root)
      unless result.usage == (← get).budget.consumed do
        throwError "packed context omitted construction charges"
      seen.set (some result)
      return ⟨result.context,result.checked,result.usage⟩
    let .ok quoted ← RootQuote.runWith action | throwError "native context packing declined"
    let some packed ← seen.get | throwError "native context result was not retained"
    let config : Hex.RealFormula.Reify.Config := {}
    let exactConfig := {config with ring := {config.ring with budget :=
      {config.ring.budget with proofNodes := quoted.usage.proofNodes}}}
    let .ok repeated ← RootQuote.runWith action exactConfig
      | throwError "native context packing failed at its exact budget"
    unless repeated.usage == quoted.usage do throwError "native context accounting changed"
    let small := {config with ring := {config.ring with budget :=
      {config.ring.budget with proofNodes := quoted.usage.proofNodes-1}}}
    let .error (.budget exhausted) ← RootQuote.runWith action small
      | throwError "native context packing did not exhaust one below its budget"
    unless exhausted.dimension == .proofNodes do throwError "native context exhausted another resource"
    let declaration := Declaration.defnDecl {
      name := `Hex.RCF.RootContextCases.child,levelParams := [],
      type := ← inferType packed.context,value := packed.context,hints := .regular 0,safety := .safe}
    withExporting (isExporting := true) do
      addDecl declaration (forceExpose := true)
      compileDecl declaration (logErrors := true)
    for (name,proof) in [(`Hex.RCF.RootContextCases.context_checked,packed.checked),
        (`Hex.RCF.RootContextCases.signature_checked,packed.binding)] do
      let kind ← inferType proof
      withExporting (isExporting := true) do
        addDecl (.thmDecl {name,levelParams := [],type := kind,value := proof})
    let model ← RealModel.build (mkConst `Hex.RCF.RootContextCases.child)
      (mkConst ``RootQuoteTests.realModel)
    let modelType ← mkAppOptM ``Tower.Model
      #[none,some (mkConst `Hex.RCF.RootContextCases.child),some (mkConst ``Real),none,none]
    let modelDeclaration := Declaration.defnDecl {
      name := `Hex.RCF.RootContextCases.model,levelParams := [],type := modelType,
      value := model,hints := .regular 0,safety := .safe}
    withExporting (isExporting := true) do
      addDecl modelDeclaration (forceExpose := true)
      modifyEnv (addNoncomputable · `Hex.RCF.RootContextCases.model)
    let value ← mkAppM ``Tower.Model.value
      #[mkConst `Hex.RCF.RootContextCases.model,mkConst ``RootHeaderPacket.coefficient]
    let equation ← mkAppM ``Tower.Model.root_value #[packed.chain,
      mkConst ``RootQuoteTests.realModel,mkConst ``RootHeaderPacket.root,
      packed.frame,packed.encoded,mkConst ``RootHeaderPacket.coefficient]
    let statement ← mkEq value (mkConst ``RootHeaderPacket.realRoot)
    let proof ← mkEqTrans equation (mkConst ``RootHeaderPacket.coefficient_value)
    let proof ← Hex.RCF.checkProof `nativeContextValue statement (mkExpectedPropHint proof statement)
    let same ← mkEqTrans proof (← mkEqSymm (mkConst ``RootHeaderPacket.coefficient_value))
    let comparison ← withLocalDeclD `value (mkConst ``Real) fun value => do
      let body ← mkLt (← mkAppOptM ``Zero.zero #[some (mkConst ``Real),none]) value
      mkLambdaFVars #[value] body
    let positive ← mkAppM ``Eq.mpr #[← mkAppM ``congrArg #[comparison,same],
      mkConst ``RootHeaderPacket.coefficient_positive]
    let positiveStatement ← mkLt (← mkAppOptM ``Zero.zero #[some (mkConst ``Real),none]) value
    let positive ← Hex.RCF.checkProof `nativeContextPositive positiveStatement positive
    withExporting (isExporting := true) do
      addDecl (.thmDecl {
        name := `Hex.RCF.RootContextCases.value_checked,levelParams := [],type := statement,value := proof})
      addDecl (.thmDecl {
        name := `Hex.RCF.RootContextCases.positive_checked,levelParams := [],
        type := positiveStatement,value := positive})
    logInfo m!"native context packing exact/one-below budget checked; proofNodes={quoted.usage.proofNodes}"
    logInfo "packed ordinary-real model retains the exact selected coefficient value and positive sign"

run_meta do
  let sentinel ← mkFreshExprMVar (mkConst ``Nat)
  let before ← getMCtx
  let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let refused ← try
    let _ ← RootQuote.runWith do
      sentinel.mvarId!.assign (mkNatLit 9)
      let _ ← mkFreshExprMVar (mkConst ``Nat)
      let statement ← mkEq (mkNatLit 0) (mkNatLit 0)
      let proof ← mkEqRefl (mkNatLit 0)
      addDecl (.thmDecl {
        name := `Hex.RCF.RootContextCases.failureMarker,levelParams := [],type := statement,value := proof})
      let result ← RootContext.packWith (mkConst ``child) (mkConst ``RootHeaderPacket.root)
      return ⟨result.context,result.checked,result.usage⟩
    pure false
  catch error =>
    if error.isInterrupt || error.isMaxHeartbeat || error.isMaxRecDepth then throw error
    unless (← error.toMessageData.toString).contains "rootData" do throw error
    pure true
  unless refused do throwError "a descriptor was packed into the wrong parent carrier"
  let after ← getMCtx
  unless !(← sentinel.mvarId!.isAssigned) && before.mvarCounter == after.mvarCounter &&
      before.lmvarCounter == after.lmvarCounter &&
      before.eAssignment.toList == after.eAssignment.toList &&
      before.lAssignment.toList == after.lAssignment.toList &&
      before.decls.toList.map Prod.fst == after.decls.toList.map Prod.fst &&
      (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
    throwError "wrong native parent retained caller state"
  logInfo "wrong native parent rejects and restores caller assignments and declarations"

run_meta do
  let descriptor ← mkFreshExprMVar (← inferType (mkConst ``RootHeaderPacket.root))
  let before ← getMCtx
  let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let refused ← try
    let _ ← RootQuote.runWith do
      let result ← RootContext.packWith (mkConst ``RootQuoteTests.base) descriptor
      return ⟨result.context,result.checked,result.usage⟩
    pure false
  catch error =>
    if error.isInterrupt || error.isMaxHeartbeat || error.isMaxRecDepth then throw error
    unless (← error.toMessageData.toString).contains "closed retained inputs" do throw error
    pure true
  unless refused do throwError "unresolved root input was accepted"
  let after ← getMCtx
  unless !(← descriptor.mvarId!.isAssigned) && before.mvarCounter == after.mvarCounter &&
      before.lmvarCounter == after.lmvarCounter &&
      before.eAssignment.toList == after.eAssignment.toList &&
      before.lAssignment.toList == after.lAssignment.toList &&
      before.decls.toList.map Prod.fst == after.decls.toList.map Prod.fst &&
      (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
    throwError "unresolved root input changed caller state"
  logInfo "unresolved native root rejects without assigning caller metavariables"

end Hex.RCF.RootContextCases
