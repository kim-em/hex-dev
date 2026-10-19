/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.EnumeratedSource.Inputs
import HexRCF.RealCoefficients.SourceIdentityQuote
import HexRCF.RealCoefficients.RootHeader
import HexRCF.RealCoefficients.RootPrepare
import HexRCF.RealCoefficients.RationalQuote

/-! Restore enumerated source proposals from literal descriptors and graphs.
The native producer and its selected-root value never enter these proofs. The
rational model, source alias selection and coefficient-map laws remain inputs. -/
namespace Hex.RCF.EnumeratedSourceQuote
open Lean Meta Qq Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests Hex.RCF.SourceIdentityCases Hex.RCF.EnumeratedSourceInputs
set_option maxRecDepth 32768
set_option maxHeartbeats 60000000

private meta def quote (literal : Name) (anchor : SourceIdentity.Anchor)
    (equationValue enclosureValue : Expr) : Hex.RealFormula.Reify.ReifyM RootQuote.Result := do
  let decode : RootQuote.DecoderM := fun expression =>
    liftM (RationalQuote.decoder (mkConst ``Data.registry) expression)
  let reader ← mkAppM ``Algebraic.RootReplay.readDescriptor
    #[q(Data.base.codec),q(Tower.Signature.codec),q(Data.base.sign),q(Data.base.signature),
      mkConst (literal ++ `subject),mkConst (literal ++ `graph)]
  let header ← RootHeader.quoteWith reader decode
  let clean ← mkAppM ``Tower.Context.isClean #[mkConst ``Data.base]
  let prepared ← RootPrepare.prepareWith header clean
  let scalar (polynomial sign graph : Expr) : MetaM Expr := do
    mkAppM ``ScalarPacket.read #[mkConst ``Data.rational,q(Data.base.codec),prepared.source,
      polynomial,sign,graph]
  let packets : SourceIdentity.Packets := {
    equation := ← scalar (mkConst (literal ++ `equation)) (toExpr (0 : Int))
      (mkConst (literal ++ `equationGraph))
    enclosure := ← scalar (mkConst (literal ++ `margin)) (toExpr (1 : Int))
      (mkConst (literal ++ `marginGraph))
    equationValue, enclosureValue }
  let result ← SourceIdentity.quoteWith anchor packets prepared.context prepared.same
    fun expression => do
      if let some result ← prepared.decoder expression then return some result
      decode expression
  return ⟨result.root,result.proof,(← get).budget.consumed⟩

private meta def retain (name : Name) (literal : Name) (anchor : SourceIdentity.Anchor)
    (equationValue enclosureValue : Expr) : MetaM Unit := do
  let basic : Hex.RealFormula.Reify.Config := {}
  -- These all-real derivative descriptors are larger than the old interval
  -- fixture. Use the existing full-source test envelope explicitly; the
  -- library default and the original full-source test remain unchanged.
  let config := {basic with ring := {basic.ring with budget :=
    {basic.ring.budget with proofNodes := 24000000}}}
  let result ← RootQuote.runWith (quote literal anchor equationValue enclosureValue) config
  let result ← match result with
    | .ok result => pure result
    | .error error => throwError "enumerated source quotation refused: {Hex.RealFormula.Reify.Error.toMessageData error}"
  let target ← inferType result.proof
  let proof ← Hex.RCF.checkProof `enumeratedSource target result.proof
  addDecl (.thmDecl {name,levelParams := [],type := target,value := proof})
  let axioms ← collectAxioms name
  unless axioms.all (fun name => [``propext,``Classical.choice,``Quot.sound].contains name) do
    throwError "enumerated source quotation has inadmissible dependencies"
  logInfo m!"enumerated source {name}: proofNodes={result.usage.proofNodes}; axioms={axioms}"

run_meta do
  withoutExporting do
    let positive : SourceIdentity.Anchor := {
      polynomial := mkConst ``SquareTwo.polynomial
      square := mkConst ``SquareTwo.square
      witness := mkConst ``positiveWitness
      precision := mkConst ``positivePrecision
      value := q(Real.sqrt 2)
      selected := mkConst ``SquareTwo.square_selected_root }
    retain `Hex.RCF.EnumeratedSourceQuote.positive
      `Hex.RCF.RealCoefficients.EnumeratedSource.Positive positive
      (mkConst ``positiveEquation) (mkConst ``positiveMargin)
    let negative : SourceIdentity.Anchor := {positive with
      square := mkConst ``negativeSquare
      witness := mkConst ``negative_witness
      precision := mkConst ``negative_precision
      value := q((Field.literalRep SquareTwo.polynomial negativeSquare
        negative_witness negative_precision).root.re)
      selected := ← mkEqRefl q((Field.literalRep SquareTwo.polynomial negativeSquare
        negative_witness negative_precision).root.re) }
    retain `Hex.RCF.EnumeratedSourceQuote.negative
      `Hex.RCF.RealCoefficients.EnumeratedSource.Negative negative
      (mkConst ``negativeEquation) (mkConst ``negativeMargin)
    let cubic : SourceIdentity.Anchor := {
      polynomial := mkConst ``CubeTwo.polynomial
      square := mkConst ``CubeTwo.square
      witness := mkConst ``cubicWitness
      precision := mkConst ``cubicPrecision
      value := q((2 : ℝ) ^ (1 / 3 : ℝ))
      selected := mkConst ``cubicSelected }
    retain `Hex.RCF.EnumeratedSourceQuote.cubic
      `Hex.RCF.RealCoefficients.EnumeratedSource.Cubic cubic
      (mkConst ``cubicEquation) (mkConst ``cubicMargin)

end Hex.RCF.EnumeratedSourceQuote
