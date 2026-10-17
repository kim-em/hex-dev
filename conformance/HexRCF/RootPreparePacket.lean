/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RootHeaderPacket
public meta import HexRCF.RealCoefficients.RootPrepare
public meta import HexRCF.RealCoefficients.ScalarPacketQuote
public meta import HexRCF.RealCoefficients.SignatureQuote
public meta import HexRCF.RealCoefficients.RationalQuote
public section

/-! Quote an original anonymous cubic reader using retained native data and
independently checked header bindings, within one reflection request. -/
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.RootPreparePacket
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

meta def config : Hex.RealFormula.Reify.Config :=
  let basic : Hex.RealFormula.Reify.Config := {}
  {basic with ring := {basic.ring with budget :=
    {basic.ring.budget with proofNodes := 3000000}}}

/-- The sign is a proposal, checked against the original frozen packet. -/
meta def quoteWith (sign : Int := 1) : Hex.RealFormula.Reify.ReifyM RootQuote.Result := do
  let some original ← unfoldDefinition? (mkConst ``RootQuoteTests.read)
    | throwError "original descriptor reader is not exposed"
  let base : RootQuote.DecoderM := fun expression =>
    liftM (RationalQuote.decoder (mkConst ``RootQuoteTests.registry) expression)
  let header ← RootHeader.quoteWith original base
  if header.root.value.isConst then throwError "anonymous descriptor regression lost its inline input"
  let clean ← mkAppM ``Tower.Context.isClean #[mkConst ``RootQuoteTests.base]
  let prepared ← RootPrepare.prepareWith header clean
  unless prepared.usage == (← get).budget.consumed do
    throwError "native preparation omitted resource charges"
  unless prepared.root.isConst && prepared.context.isConst &&
      prepared.source.getAppFn.isConstOf ``Algebraic.Context.adjoin do
    throwError "native preparation did not retain the original anonymous context"
  let signature ← mkAppM ``Tower.Context.signature #[mkConst ``RootQuoteTests.base]
  let decode : RootQuote.DecoderM := fun expression => do
    if let some proof ← SignatureQuote.decoder signature
        (mkConst ``RootHeaderPacket.signatureData)
        (mkConst ``RootHeaderPacket.signature_literal) expression then
      return some proof
    if let some proof ← prepared.decoder expression then return some proof
    liftM (RationalQuote.decoder (mkConst ``RootQuoteTests.registry) expression)
  let codec ← mkAppM ``Tower.Context.codec #[mkConst ``RootQuoteTests.base]
  let reader ← mkAppM ``ScalarPacket.read
    #[mkConst ``RootHeaderPacket.model,codec,prepared.source,
      mkConst ``RootHeaderPacket.polynomial,mkIntLit sign,mkConst ``RootHeaderPacket.evidence]
  let quoted ← ScalarPacket.quoteWith reader prepared.context prepared.same decode
  let target ← mkEq reader (← mkAppM ``Option.some #[quoted.value])
  Hex.RealFormula.Reify.accountProof target
  Hex.RealFormula.Reify.accountProof quoted.proof
  let proof ← Hex.RCF.checkProof `RootPreparePacket.original target quoted.proof
  return {quoted with proof,usage := (← get).budget.consumed}

/-- Export data names in theorem types; their private construction proofs stay
in definition bodies. The original anonymous reader was checked before this
definitionally equal public presentation is constructed. -/
meta def publishWith (quoted : RootQuote.Result) : Hex.RealFormula.Reify.ReifyM RootQuote.Result := do
  let kind ← inferType quoted.proof
  unless kind.isAppOfArity ``Eq 3 do throwError "original packet proof is not an equation"
  let reader := kind.getAppArgs[1]!
  unless reader.getAppFn.isConstOf ``ScalarPacket.read do
    throwError "original packet proof has a different reader"
  let declaration ← getConstInfo ``ScalarPacket.read
  let index ← forallTelescope declaration.type fun binders _ => do
    for index in [:binders.size] do
      if (← getFVarLocalDecl binders[index]!).userName == `context then return index
    throwError "scalar reader has no context binder"
  let arguments := reader.getAppArgs
  let source := arguments[index]!
  let contextName := `Hex.RCF.RootPreparePacket.context
  let contextType ← inferType source
  Hex.RealFormula.Reify.accountProof source
  Hex.RealFormula.Reify.accountProof contextType
  withExporting (isExporting := true) do
    let data := Declaration.defnDecl {
      name := contextName,levelParams := [],type := contextType,value := source,
      hints := .regular (getMaxHeight (← getEnv) source+1),safety := .safe}
    addDecl data (forceExpose := true)
    compileDecl data (logErrors := true)
  let publicReader := mkAppN reader.getAppFn (arguments.set! index (mkConst contextName))
  let optional ← inferType publicReader
  unless optional.isAppOfArity ``Option 1 do throwError "public packet reader is not optional"
  let factType := optional.appArg!
  Hex.RealFormula.Reify.accountProof factType
  Hex.RealFormula.Reify.accountProof quoted.value
  let factName := `Hex.RCF.RootPreparePacket.fact
  withExporting (isExporting := true) do
    let data := Declaration.defnDecl {
      name := factName,levelParams := [],type := factType,value := quoted.value,
      hints := .regular (getMaxHeight (← getEnv) quoted.value+1),safety := .safe}
    addDecl data (forceExpose := true)
    compileDecl data (logErrors := true)
  let target ← mkEq publicReader (← mkAppM ``Option.some #[mkConst factName])
  Hex.RealFormula.Reify.accountProof target
  let candidate := mkExpectedPropHint quoted.proof target
  Hex.RealFormula.Reify.accountProof candidate
  let proof ← Hex.RCF.checkProof `RootPreparePacket.public target candidate
  return ⟨mkConst factName,proof,(← get).budget.consumed⟩

run_meta do
  withoutExporting do
    let result ← match ← RootQuote.runWith (do
        let quoted ← quoteWith 1
        publishWith quoted) config with
      | .ok result => pure result
      | .error error => throwError "retained original packet: {Hex.RealFormula.Reify.Error.toMessageData error}"
    let axioms ← collectAxioms result.proof.getAppFn.constName!
    unless axioms.all (fun name => [``propext,``Classical.choice,``Quot.sound].contains name) do
      throwError "retained packet axiom closure changed: {axioms}"
    let kind ← inferType result.proof
    withExporting (isExporting := true) do
      addDecl (.thmDecl {
        name := `Hex.RCF.RootPreparePacket.read_checked,levelParams := [],type := kind,value := result.proof})
    logInfo m!"original anonymous packet, full request proof budget={result.usage.proofNodes}; axioms={axioms}"

end Hex.RCF.RootPreparePacket
