/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.SourceIdentityLiterals
import HexRCF.SourceIdentityCases
import HexRCF.RealCoefficients.SourceIdentityQuote
import HexRCF.RealCoefficients.RootHeader
import HexRCF.RealCoefficients.RootPrepare
import HexRCF.RealCoefficients.RationalQuote
open Lean Meta Qq Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests Hex.RCF.SourceIdentityCases
namespace Hex.RCF.SourceIdentityPacket
open Hex.RCF.SelectedRootTests.SourceIdentityPackets
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem witness : atomWitness SquareTwo.polynomial SquareTwo.square := by decide +kernel
theorem precision : (mahlerPrec SquareTwo.polynomial : Int) ≤ SquareTwo.square.prec := by decide +kernel

theorem equation_value :
    HexPolyTheory.Interpret.interpret Data.rational.value Data.rational.zero_iff
      (ScalarPacket.key Data.base.codec packet0.1) =
      LiteralSign.realPoly (ZPoly.toRatPoly SquareTwo.polynomial) := by
  have parsed : ScalarPacket.key Data.base.codec packet0.1 =
      embed (ZPoly.toRatPoly SquareTwo.polynomial) := by decide +kernel
  rw [parsed]
  exact embed_value _

theorem enclosure_value :
    HexPolyTheory.Interpret.interpret Data.rational.value Data.rational.zero_iff
      (ScalarPacket.key Data.base.codec packet1.1) =
      LiteralSign.realPoly (SourceIdentity.margin SquareTwo.square) := by
  have parsed : ScalarPacket.key Data.base.codec packet1.1 =
      embed (SourceIdentity.margin SquareTwo.square) := by decide +kernel
  rw [parsed]
  exact embed_value _

theorem negative_value :
    HexPolyTheory.Interpret.interpret Data.rational.value Data.rational.zero_iff
      (ScalarPacket.key Data.base.codec packet2.1) =
      LiteralSign.realPoly (SourceIdentity.margin negativeSquare) := by
  have parsed : ScalarPacket.key Data.base.codec packet2.1 =
      embed (SourceIdentity.margin negativeSquare) := by decide +kernel
  rw [parsed]
  exact embed_value _

meta def inputs : MetaM (SourceIdentity.Anchor × SourceIdentity.Packets) := do
  let anchor : SourceIdentity.Anchor := {
    polynomial := mkConst ``SquareTwo.polynomial
    square := mkConst ``SquareTwo.square
    witness := mkConst ``witness
    precision := mkConst ``precision
    value := q(Real.sqrt 2)
    selected := mkConst ``SquareTwo.square_selected_root }
  let reader (packet : Expr) : MetaM Expr := do
    let polynomial ← mkAppM ``Prod.fst #[packet]
    let rest ← mkAppM ``Prod.snd #[packet]
    let sign ← mkAppM ``Prod.fst #[rest]
    let graph ← mkAppM ``Prod.snd #[rest]
    mkAppM ``ScalarPacket.read #[mkConst ``Data.rational,q(Data.base.codec),
      mkConst ``Data.native,polynomial,sign,graph]
  let packets : SourceIdentity.Packets := {
    equation := ← reader (mkConst ``packet0)
    enclosure := ← reader (mkConst ``packet1)
    equationValue := mkConst ``equation_value
    enclosureValue := mkConst ``enclosure_value }
  return (anchor,packets)

meta def withParent
    (consume : Expr → Expr → RootQuote.DecoderM → Hex.RealFormula.Reify.ReifyM RootQuote.Result) :
    Hex.RealFormula.Reify.ReifyM RootQuote.Result := do
  let decode : RootQuote.DecoderM := fun expression =>
    liftM (RationalQuote.decoder (mkConst ``Data.registry) expression)
  let some original ← unfoldDefinition? (mkConst ``Data.lowerRead)
    | throwError "original root reader unavailable"
  let header ← RootHeader.quoteWith original decode
  let clean ← mkAppM ``Tower.Context.isClean #[mkConst ``Data.base]
  let prepared ← RootPrepare.prepareWith header clean
  let rootEq ← mkAppM ``Option.get_of_eq_some #[mkConst ``Data.lowerAccepted,header.root.proof]
  let contextFn ← withLocalDeclD `root (← inferType (mkConst ``Data.lower)) fun root => do
    mkLambdaFVars #[root] (← mkAppM ``Algebraic.Context.adjoin #[root,clean])
  let contextEq ← mkAppM ``congrArg #[contextFn,rootEq]
  let same ← mkEqTrans contextEq prepared.same
  consume prepared.context same fun expression => do
    if let some proof ← prepared.decoder expression then return some proof
    decode expression

meta def quoteSource (anchor : SourceIdentity.Anchor) (packets : SourceIdentity.Packets) :
    Hex.RealFormula.Reify.ReifyM RootQuote.Result :=
  withParent fun context same decode => do
    let quoted ← SourceIdentity.quoteWith anchor packets context same decode
    pure ⟨anchor.value,quoted.proof,quoted.usage⟩

run_meta do
  withoutExporting do
    let (anchor,packets) ← inputs
    let result ← RootQuote.runWith (quoteSource anchor packets)
    let quoted ← match result with
      | .ok result => pure result
      | .error error => throwError "source identity quotation refused: {Hex.RealFormula.Reify.Error.toMessageData error}"
    let target : Q(Prop) := q(Data.selectedReal = Real.sqrt 2)
    let proof ← Hex.RCF.checkProof `selectedOriginal target (mkExpectedPropHint quoted.proof target)
    withExporting (isExporting := true) do
      addDecl (.thmDecl {
        name := `Hex.RCF.SourceIdentityPacket.selected,levelParams := [],type := target,value := proof})
    let axioms ← collectAxioms `Hex.RCF.SourceIdentityPacket.selected
    unless axioms.all (fun name => [``propext,``Classical.choice,``Quot.sound].contains name) do
      throwError "quoted source selection has inadmissible dependencies"
    logInfo m!"quoted source selection proofNodes={quoted.usage.proofNodes}; axioms={axioms}"

theorem coefficient : Data.original.value Data.alpha = Real.sqrt 2 := by
  rw [← Data.generator_eq]
  exact (Data.rational.root_generator (.base (BaseContext.rational Data.registry))
    Data.lower Data.frozenFrame Data.frameEncoded).trans selected
end Hex.RCF.SourceIdentityPacket
