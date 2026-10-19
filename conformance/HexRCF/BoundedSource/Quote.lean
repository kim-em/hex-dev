/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.BoundedSource.Inputs
import HexRCF.RealCoefficients.SourceIdentityQuote
import HexRCF.RealCoefficients.RootHeader
import HexRCF.RealCoefficients.RootPrepare
import HexRCF.RealCoefficients.RationalQuote

/-! Restore bounded source proposals from literal descriptors and graphs.
The native producer and its selected-root value never enter these proofs. The
rational model, source alias selection and coefficient-map laws remain inputs. -/
namespace Hex.RCF.BoundedSourceQuote
open Lean Meta Qq Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests Hex.RCF.SourceIdentityCases Hex.RCF.BoundedSourceInputs
set_option maxRecDepth 32768
set_option maxHeartbeats 60000000

private meta def quote (literal : Name) (anchor : SourceIdentity.Anchor)
    (equationValue enclosureValue : Expr)
    (change : SourceIdentity.Packet → SourceIdentity.Packet := id)
    (model : Expr := mkConst ``Data.rational) : Hex.RealFormula.Reify.ReifyM RootQuote.Result := do
  let decode : RootQuote.DecoderM := fun expression =>
    liftM (RationalQuote.decoder (mkConst ``Data.registry) expression)
  let packet : SourceIdentity.Packet := {
    subject := mkConst (literal ++ `subject)
    graph := mkConst (literal ++ `graph)
    equation := mkConst (literal ++ `equation)
    equationGraph := mkConst (literal ++ `equationGraph)
    enclosure := mkConst (literal ++ `margin)
    enclosureGraph := mkConst (literal ++ `marginGraph)
    equationValue, enclosureValue }
  let result ← SourceIdentity.quotePacketWith anchor (change packet)
    (mkConst ``Data.base) model decode
  return ⟨result.root,result.proof,(← get).budget.consumed⟩

private meta def retain (name : Name) (literal : Name) (anchor : SourceIdentity.Anchor)
    (equationValue enclosureValue : Expr) : MetaM Unit := do
  let result ← RootQuote.runWith (quote literal anchor equationValue enclosureValue)
  let result ← match result with
    | .ok result => pure result
    | .error error => throwError "bounded source quotation refused: {Hex.RealFormula.Reify.Error.toMessageData error}"
  let target ← inferType result.proof
  let proof ← Hex.RCF.checkProof `boundedSource target result.proof
  addDecl (.thmDecl {name,levelParams := [],type := target,value := proof})
  let axioms ← collectAxioms name
  unless axioms.all (fun name => [``propext,``Classical.choice,``Quot.sound].contains name) do
    throwError "bounded source quotation has inadmissible dependencies"
  logInfo m!"bounded source {name}: proofNodes={result.usage.proofNodes}; axioms={axioms}"
  if name == `Hex.RCF.BoundedSourceQuote.positive then
    let sentinel ← mkFreshExprMVar (mkConst ``Nat)
    let before ← getMCtx
    let config : Hex.RealFormula.Reify.Config := {}
    let exact := {config with ring := {config.ring with budget :=
      {config.ring.budget with proofNodes := result.usage.proofNodes}}}
    let action : Hex.RealFormula.Reify.ReifyM RootQuote.Result := do
      sentinel.mvarId!.assign (mkNatLit 96)
      quote literal anchor equationValue enclosureValue
    let .ok repeated ← RootQuote.runWith action exact
      | throwError "assembled source rejected its exact charged budget"
    unless repeated.usage == result.usage && !(← sentinel.mvarId!.isAssigned) do
      throwError "assembled source exact-budget usage or success restoration changed"
    let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
    let small := {config with ring := {config.ring with budget :=
      {config.ring.budget with proofNodes := result.usage.proofNodes-1}}}
    let .error (.budget exhausted) ← RootQuote.runWith action small
      | throwError "bounded source accepted below its charged budget"
    unless exhausted.dimension == .proofNodes do throwError "wrong bounded source budget dimension"
    let after ← getMCtx
    unless !(← sentinel.mvarId!.isAssigned) && before.mvarCounter == after.mvarCounter &&
        before.lmvarCounter == after.lmvarCounter && before.eAssignment.toList == after.eAssignment.toList &&
        before.lAssignment.toList == after.lAssignment.toList &&
        before.decls.toList.map Prod.fst == after.decls.toList.map Prod.fst &&
        (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
      throwError "bounded source exhaustion retained metavariables or declarations"
    logInfo m!"bounded source below-budget refusal and state restoration: limit={result.usage.proofNodes-1}"
    let wrongValue ← mkEqRefl (mkConst ``Bool.false)
    let bad : Array (String × (SourceIdentity.Packet → SourceIdentity.Packet) × Expr) := #[
      ("descriptor binding", fun p => {p with
        subject := mkConst `Hex.RCF.RealCoefficients.BoundedSource.Negative.subject}, mkConst ``Data.rational),
      ("equation sign", fun p => {p with equationGraph := p.enclosureGraph}, mkConst ``Data.rational),
      ("coefficient law", fun p => {p with equationValue := wrongValue}, mkConst ``Data.rational),
      ("parent model", id, mkConst ``Data.original)]
    for (label,change,model) in bad do
      let before ← getMCtx
      let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
      let refused ← try
          match ← RootQuote.runWith (do
            sentinel.mvarId!.assign (mkNatLit 97)
            quote literal anchor equationValue enclosureValue change model) config with
          | .ok _ => pure false
          | .error _ => pure true
        catch _ => pure true
      unless refused do throwError "assembled source accepted {label}"
      let after ← getMCtx
      unless !(← sentinel.mvarId!.isAssigned) && before.mvarCounter == after.mvarCounter &&
          before.lmvarCounter == after.lmvarCounter && before.eAssignment.toList == after.eAssignment.toList &&
          before.lAssignment.toList == after.lAssignment.toList &&
          before.decls.toList.map Prod.fst == after.decls.toList.map Prod.fst &&
          (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
        throwError "assembled source failure retained state: {label}"
      logInfo m!"assembled source refused {label}; metavariables and declarations restored"

run_meta do
  withoutExporting do
    let positive : SourceIdentity.Anchor := {
      polynomial := mkConst ``SquareTwo.polynomial
      square := mkConst ``SquareTwo.square
      witness := mkConst ``positiveWitness
      precision := mkConst ``positivePrecision
      value := q(Real.sqrt 2)
      selected := mkConst ``SquareTwo.square_selected_root }
    retain `Hex.RCF.BoundedSourceQuote.positive
      `Hex.RCF.RealCoefficients.BoundedSource.Positive positive
      (mkConst ``positiveEquation) (mkConst ``positiveMargin)
    let negative : SourceIdentity.Anchor := {positive with
      square := mkConst ``negativeSquare
      witness := mkConst ``negative_witness
      precision := mkConst ``negative_precision
      value := q((Field.literalRep SquareTwo.polynomial negativeSquare
        negative_witness negative_precision).root.re)
      selected := ← mkEqRefl q((Field.literalRep SquareTwo.polynomial negativeSquare
        negative_witness negative_precision).root.re) }
    retain `Hex.RCF.BoundedSourceQuote.negative
      `Hex.RCF.RealCoefficients.BoundedSource.Negative negative
      (mkConst ``negativeEquation) (mkConst ``negativeMargin)
    let cubic : SourceIdentity.Anchor := {
      polynomial := mkConst ``CubeTwo.polynomial
      square := mkConst ``CubeTwo.square
      witness := mkConst ``cubicWitness
      precision := mkConst ``cubicPrecision
      value := q((2 : ℝ) ^ (1 / 3 : ℝ))
      selected := mkConst ``cubicSelected }
    retain `Hex.RCF.BoundedSourceQuote.cubic
      `Hex.RCF.RealCoefficients.BoundedSource.Cubic cubic
      (mkConst ``cubicEquation) (mkConst ``cubicMargin)

end Hex.RCF.BoundedSourceQuote
