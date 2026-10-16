/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RationalQuoteData
public meta import HexRCF.RealCoefficients.RationalQuote
public section
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.RationalQuoteTests
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192

private meta def scalar (n d : Int) (tag : Int := 0) : Expr :=
  let numbers := [tag,n,d].foldr (fun i rest =>
    mkApp2 (mkConst ``Codec.Json.Values.cons)
      (mkApp (mkConst ``Codec.Json.Value.number) (mkIntLit i)) rest)
    (mkConst ``Codec.Json.Values.nil)
  mkApp (mkConst ``Codec.Json.Value.array) numbers

run_meta do
  withExporting (isExporting := false) do
    let registry := mkConst ``Hex.RCF.RootQuoteTests.registry
    let context ← mkAppM ``Hex.RealClosure.NumberField.base #[registry]
    let codec ← mkAppM ``Tower.Context.codec #[context]
    let mut index := 0
    for (n,d) in ([(0,1),(7,3),(-7,3),(17,13),(123456789,100000000)] : List (Int × Int)) do
      let reader := mkApp (.proj ``ValueCodec 1 codec) (scalar n d)
      let some proof ← RationalQuote.decoder registry reader | throwError "canonical fraction declined: {n}/{d}"
      let type ← inferType proof
      unless proof.getUsedConstants.contains ``Hex.RealClosure.NumberField.decode_payload do
        throwError "fraction decoder did not use the owner equation"
      let statement ← mkEq reader type.getAppArgs[2]!
      let _ ← Hex.RCF.checkProof `canonicalFraction statement (mkExpectedPropHint proof statement)
      withExporting (isExporting := true) do
        addDecl (.thmDecl {
          name := Name.num `Hex.RCF.RationalQuoteTests.fraction_decode index,
          levelParams := [], type := statement, value := mkExpectedPropHint proof statement})
      let .ok result ← RootQuote.quote reader (RationalQuote.decoder registry)
        | throwError "canonical fraction quotation failed: {n}/{d}"
      let _ ← Hex.RCF.checkProof `quotedFraction (← inferType result.proof) result.proof
      withExporting (isExporting := true) do
        let valueName := Name.num `Hex.RCF.RationalQuoteTests.fraction_value index
        addDecl (.defnDecl {
          name := valueName, levelParams := [], type := ← inferType result.value,
          value := result.value, hints := .regular 0, safety := .safe}) (forceExpose := true)
        let accepted ← mkEq (← mkAppM ``Except.toOption #[reader])
          (← mkAppM ``Option.some #[mkConst valueName])
        addDecl (.thmDecl {
          name := Name.num `Hex.RCF.RationalQuoteTests.fraction_read index,
          levelParams := [], type := accepted, value := mkExpectedPropHint result.proof accepted})
      index := index + 1
    for (n,d,tag) in ([(0,0,0),(2,4,0),(7,-3,0),(7,3,1)] : List (Int × Int × Int)) do
      let reader := mkApp (.proj ``ValueCodec 1 codec) (scalar n d tag)
      unless (← RationalQuote.decoder registry reader).isNone do throwError "malformed/noncanonical fraction accepted"
    let wrong := mkApp (.proj ``ValueCodec 1 (mkConst ``ValueCodec.rat)) (scalar 7 3)
    unless (← RationalQuote.decoder registry wrong).isNone do throwError "different coefficient codec accepted"
    let carrier := (← inferType codec).appArg!
    let differentEncoder ← withLocalDeclD `value carrier fun value =>
      mkLambdaFVars #[value] (mkConst ``Codec.Json.Value.null)
    let differentCodec := mkAppN (mkConst ``ValueCodec.mk)
      #[carrier,differentEncoder,.proj ``ValueCodec 1 codec]
    let sameDecode := mkApp (.proj ``ValueCodec 1 differentCodec) (scalar 7 3)
    unless ← isDefEq sameDecode (mkApp (.proj ``ValueCodec 1 codec) (scalar 7 3)) do
      throwError "different-encoder control changed its decoding function"
    unless (← RationalQuote.decoder registry sameDecode).isNone do
      throwError "decoder accepted a different codec record with the same decoding function"
    logInfo "generic decoder accepts checked fractions and declines noncanonical payloads or a different codec"

run_meta do
  withExporting (isExporting := false) do
    let .ok result ← RootQuote.quote (mkConst ``Hex.RCF.RootQuoteTests.read)
        (RationalQuote.decoder (mkConst ``Hex.RCF.RootQuoteTests.registry))
      | throwError "generic rational decoder did not quote the frozen cubic"
    let _ ← Hex.RCF.checkProof `genericCubic (← inferType result.proof) result.proof
    logInfo m!"generic rational decoder quoted frozen cubic, proofNodes={result.usage.proofNodes}"
    withExporting (isExporting := true) do
      let name := `Hex.RCF.RationalQuoteTests.nativeRoot
      addDecl (.defnDecl {
        name, levelParams := [], type := ← inferType result.value,
        value := result.value, hints := .regular 0, safety := .safe}) (forceExpose := true)
      let statement ← mkEq (← mkAppM ``Except.toOption #[mkConst ``Hex.RCF.RootQuoteTests.read])
        (← mkAppM ``Option.some #[mkConst name])
      addDecl (.thmDecl {
        name := `Hex.RCF.RationalQuoteTests.nativeRoot_read,
        levelParams := [], type := statement, value := mkExpectedPropHint result.proof statement})

run_meta do
  withExporting (isExporting := false) do
    let registry := mkConst ``Hex.RCF.RootQuoteTests.registry
    let base ← mkAppM ``Hex.RealClosure.NumberField.base #[registry]
    let codec ← mkAppM ``Tower.Context.codec #[base]
    let reader := mkApp (.proj ``ValueCodec 1 codec) (mkConst ``negativeFraction)
    let some proposed ← RationalQuote.decoder registry reader
      | throwError "frozen negative fraction declined"
    let type ← inferType proposed
    let statement ← mkEq reader type.getAppArgs[2]!
    let _ ← Hex.RCF.checkProof `frozenNegative statement (mkExpectedPropHint proposed statement)
    let .ok result ← RootQuote.quote (mkConst ``negativeReader) (RationalQuote.decoder registry)
      | throwError "frozen negative fraction quotation failed"
    withExporting (isExporting := true) do
      addDecl (.thmDecl {
        name := `Hex.RCF.RationalQuoteTests.negative_decode, levelParams := [],
        type := statement, value := mkExpectedPropHint proposed statement})
      let name := `Hex.RCF.RationalQuoteTests.negativeValue
      addDecl (.defnDecl {
        name, levelParams := [], type := ← inferType result.value,
        value := result.value, hints := .regular 0, safety := .safe}) (forceExpose := true)
      let accepted ← mkEq (← mkAppM ``Except.toOption #[mkConst ``negativeReader])
        (← mkAppM ``Option.some #[mkConst name])
      addDecl (.thmDecl {
        name := `Hex.RCF.RationalQuoteTests.negative_read, levelParams := [],
        type := accepted, value := mkExpectedPropHint result.proof accepted})
    let extension ← mkAppM ``Tower.Context.adjoin #[base,mkConst ``nativeRoot]
    let child ← mkAppM ``Tower.Extension.context #[extension]
    let childCodec ← mkAppM ``Tower.Context.codec #[child]
    let childReader := mkApp (.proj ``ValueCodec 1 childCodec) (scalar 7 3)
    let _ ← Hex.RCF.checkExpr `wellTypedChildCodec childReader
    let initial ← IO.getNumHeartbeats
    withTheReader Core.Context (fun context =>
        {context with initHeartbeats := initial, maxHeartbeats := 200000}) do
      unless (← RationalQuote.decoder registry childReader).isNone do
        throwError "rational decoder accepted a selected-root child codec"
    let failed ← try
      let _ ← RationalQuote.decoder (mkNatLit 0) reader
      pure false
    catch error =>
      match error with
      | .error _ _ => pure true
      | _ => throw error
    unless failed do throwError "rational decoder accepted an ill-typed registry"
    logInfo "frozen negative fraction quoted; well-typed selected-child codec declines within 200000 heartbeats; ill-typed registry rejected"

end Hex.RCF.RationalQuoteTests
