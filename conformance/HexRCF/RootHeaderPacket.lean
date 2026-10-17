/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.ScalarPacketQuote
public import HexRealClosureTheory.NumberFieldTower
public import HexRCF.RootQuoteCases
public import HexRCF.RootQuoteSource
public meta import HexRCF.RootQuoteData
public meta import HexRCF.RootQuoteCases
public meta import HexRCF.RootQuoteSource
public meta import HexRCF.RealCoefficients.ScalarPacketQuote
public meta import HexRCF.RealCoefficients.RationalQuote
public meta import HexRCF.RealCoefficients.RootQuote
public meta import HexRCF.RealCoefficients.RootHeader
public meta import HexRCF.RealCoefficients.SignatureQuote
public section

/-! Quote the original scalar-packet reader from a public module. Every graph
field, including complete context signatures, retains frozen JSON data. -/

open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.RootHeaderPacket
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

/- Reconstruct the root and its raw header from the original supplied reader. -/
run_meta do
  withoutExporting do
    let some original ← unfoldDefinition? (mkConst ``RootQuoteTests.read)
      | throwError "original root reader is not exposed"
    let base : RootQuote.DecoderM := fun expression =>
      liftM (RationalQuote.decoder (mkConst ``RootQuoteTests.registry) expression)
    let .ok result ← RootQuote.runWith do
        let header ← RootHeader.quoteWith original base
        for (name,value) in [(`Hex.RCF.RootHeaderPacket.root,header.root.value),
            (`Hex.RCF.RootHeaderPacket.raw,header.raw)] do
          let declaration := Declaration.defnDecl {
            name,levelParams := [],type := ← inferType value,value,
            hints := .regular 0,safety := .safe}
          withExporting (isExporting := true) do
            addDecl declaration (forceExpose := true)
            compileDecl declaration (logErrors := true)
        let statement ← mkEq
          (← mkAppM ``Descriptor.raw #[mkConst `Hex.RCF.RootHeaderPacket.root])
          (mkConst `Hex.RCF.RootHeaderPacket.raw)
        let candidate := mkExpectedPropHint header.binding statement
        Hex.RealFormula.Reify.accountProof candidate
        let proof ← Hex.RCF.checkProof `headerBinding statement candidate
        withExporting (isExporting := true) do
          addDecl (.thmDecl {
            name := `Hex.RCF.RootHeaderPacket.raw_binding,levelParams := [],type := statement,value := proof})
        return header.root
      | throwError "original root/header quotation declined"
    logInfo m!"original root/header assembled; nodes={result.usage.proofNodes}"

@[expose] def context := Algebraic.Context.adjoin Hex.RCF.RootHeaderPacket.root RootQuoteTests.base.isClean
@[expose] def polynomial : Codec.Json :=
  .array (.cons RootQuoteTests.j5 (.cons RootQuoteTests.j6 .nil))
@[expose] noncomputable def model := RootQuoteTests.realModel

/-- The complete rational predecessor identity, stored as literal data. -/
abbrev signatureData : Codec.Json :=
  .array (.cons (.array .nil) (.cons (.number 0) (.cons (.array .nil) .nil)))

theorem signature_literal : signatureData = RootQuoteTests.base.signature.literal.toJson := by
  rw [Tower.Context.base_signature]
  unfold BaseContext.rational
  rw [BaseContext.Context.signature_real,BaseContext.RealContext.keys_rational]
  rfl

/-- Construct numerical proposal data; its computation supplies no proof. -/
private meta partial def jsonExpr : Codec.Json → MetaM Expr
  | .number n =>
    let integer := if n < 0 then mkApp (mkConst ``Int.negSucc) (mkRawNatLit (n.natAbs-1))
      else mkApp (mkConst ``Int.ofNat) (mkRawNatLit n.natAbs)
    pure (mkApp (mkConst ``Codec.Json.Value.number) integer)
  | .array values => do
    let items ← values.toList.mapM jsonExpr
    let data := items.foldr
      (fun item rest => mkApp2 (mkConst ``Codec.Json.Values.cons) item rest)
      (mkConst ``Codec.Json.Values.nil)
    return mkApp (mkConst ``Codec.Json.Value.array) data
  | _ => throwError "public sign fixture expected numerical array data"


/-- Normalize demanded root bindings with the generated header equation.
Frozen signature reads use the public full-literal equation at their exact
checked subject. -/
meta def decoder : RootQuote.DecoderM := fun expression => do
  let signature ← mkAppM ``Tower.Context.signature #[mkConst ``RootQuoteTests.base]
  if let some proof ← SignatureQuote.decoder signature (mkConst ``signatureData)
      (mkConst ``signature_literal) expression then
    return some proof
  if (expression.getUsedConstants.contains ``context ||
      expression.getUsedConstants.contains ``Hex.RCF.RootHeaderPacket.root) &&
      (← withTransparency .reducible <| whnf (← inferType expression)).isConstOf ``Bool then
    let result ← liftM do
      let mut laws : SimpTheorems := {}
      laws ← laws.addDeclToUnfold ``context
      laws ← laws.addConst ``Algebraic.Context.root_adjoin
      laws ← laws.addConst ``Hex.RCF.RootHeaderPacket.raw_binding
      let simpContext ← Simp.mkContext {maxSteps := 100000} #[laws]
      let (result,_) ← Meta.simp expression simpContext
      pure result
    if result.expr != expression then
      return some (← liftM (result.getProof' expression))
  liftM (RationalQuote.decoder (mkConst ``RootQuoteTests.registry) expression)

meta def quoteConfig : Hex.RealFormula.Reify.Config :=
  let basic : Hex.RealFormula.Reify.Config := {}
  {basic with ring := {basic.ring with budget :=
    {basic.ring.budget with proofNodes := 2000000}}}

run_meta do
  withExporting (isExporting := false) do
    let codec ← mkAppM ``Tower.Context.codec #[mkConst ``RootQuoteTests.base]
    let proposal ← mkAppM ``ScalarPacket.buildLiteral
      #[mkConst ``context,codec,mkConst ``polynomial]
    let some packet ← evalExpr (Option Codec.Json) (← inferType proposal) proposal
      | throwError "public sign packet producer declined"
    let .ok fields := packet.getArr? | throwError "public packet is not an array"
    unless fields.size == 3 do throwError "public packet has the wrong width"
    let .ok sign := fields[1]!.getInt? | throwError "public packet has no sign"
    unless sign == 1 do throwError "public packet has the wrong proposed sign"
    let evidence ← jsonExpr fields[2]!
    let constructors := #[``Codec.Json.Value.number,``Codec.Json.Value.array,
      ``Codec.Json.Values.cons,``Codec.Json.Values.nil,``Int.ofNat,``Int.negSucc]
    unless evidence.getUsedConstants.all constructors.contains do
      throwError "public packet graph contains unexpected constants: {evidence.getUsedConstants.filter (fun name => !constructors.contains name)}"
    withExporting (isExporting := true) do
      let declaration := Declaration.defnDecl {
        name := `Hex.RCF.RootHeaderPacket.evidence,levelParams := [],
        type := mkConst ``Codec.Json.Value,value := evidence,hints := .regular 0,safety := .safe}
      addDecl declaration (forceExpose := true)
      compileDecl declaration (logErrors := true)
    let reader ← mkAppM ``ScalarPacket.read
      #[mkConst ``model,codec,mkConst ``context,mkConst ``polynomial,mkIntLit 1,
        mkConst `Hex.RCF.RootHeaderPacket.evidence]
    let outcome ← RootQuote.runWith (RootQuote.quoteOptionWith reader decoder) quoteConfig
    let quoted ← match outcome with
      | .ok result => pure result
      | .error error => throwError "public sign packet quotation: {Hex.RealFormula.Reify.Error.toMessageData error}"
    logInfo m!"original optional reader quoted; nodes={quoted.usage.proofNodes}"
    let factType ← inferType quoted.value
    withExporting (isExporting := true) do
      let declaration := Declaration.defnDecl {
        name := `Hex.RCF.RootHeaderPacket.fact,levelParams := [],
        type := factType,value := quoted.value,hints := .regular 0,safety := .safe}
      addDecl declaration (forceExpose := true)
      compileDecl declaration (logErrors := true)
    let statement ← mkEq reader (← mkAppM ``Option.some #[mkConst `Hex.RCF.RootHeaderPacket.fact])
    let proof ← Hex.RCF.checkProof `publicSignPacket statement quoted.proof
    withExporting (isExporting := true) do
      addDecl (.thmDecl {
        name := `Hex.RCF.RootHeaderPacket.read_checked,levelParams := [],type := statement,value := proof})
    logInfo m!"ordinary module sign packet proofNodes={quoted.usage.proofNodes}"
    logInfo "public scalar graph retains frozen numerical node and nested-moment signatures"

theorem accepted :
    (ScalarPacket.read model RootQuoteTests.base.codec context polynomial 1 evidence).isSome = true := by
  rw [read_checked]
  rfl

theorem sign : fact.sign = 1 :=
  (ScalarPacket.fields model RootQuoteTests.base.codec context polynomial 1 evidence fact read_checked).2

end Hex.RCF.RootHeaderPacket
