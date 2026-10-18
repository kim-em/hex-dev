/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.SourceIdentityPacket
open Lean Meta Qq Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests Hex.RCF.SourceIdentityCases
open Hex.RCF.SourceIdentityPacket
namespace Hex.RCF.SourceIdentityControls
open Hex.RCF.SelectedRootTests.SourceIdentityPackets
set_option maxRecDepth 32768
set_option maxHeartbeats 32000000

private meta def restored (before : MetavarContext) (sentinel : Expr)
    (names : Option (Array Name) := none) : MetaM Unit := do
  let after ← getMCtx
  unless !(← sentinel.mvarId!.isAssigned) && before.mvarCounter == after.mvarCounter &&
      before.lmvarCounter == after.lmvarCounter && before.eAssignment.toList == after.eAssignment.toList &&
      before.lAssignment.toList == after.lAssignment.toList &&
      before.decls.toList.map Prod.fst == after.decls.toList.map Prod.fst do
    throwError "source identity quotation retained caller metavariables"
  if let some names := names then
    unless (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
      throwError "failed source identity quotation retained declarations"

run_meta do
  withoutExporting do
    let (anchor,packets) ← inputs
    let basic : Hex.RealFormula.Reify.Config := {}
    let config := {basic with ring := {basic.ring with budget :=
      {basic.ring.budget with proofNodes := 2000000}}}
    let sentinel ← mkFreshExprMVar (mkConst ``Nat)
    let before ← getMCtx
    let action : Hex.RealFormula.Reify.ReifyM RootQuote.Result := do
      sentinel.mvarId!.assign (mkNatLit 96)
      quoteSource anchor packets
    let .ok baseline ← RootQuote.runWith action config
      | throwError "source identity baseline refused"
    restored before sentinel
    let exact := {config with ring := {config.ring with budget :=
      {config.ring.budget with proofNodes := baseline.usage.proofNodes}}}
    let .ok repeated ← RootQuote.runWith action exact
      | throwError "source identity rejected its exact budget"
    unless repeated.usage == baseline.usage do throwError "source identity usage changed"
    restored before sentinel
    let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
    let small := {exact with ring := {exact.ring with budget :=
      {exact.ring.budget with proofNodes := baseline.usage.proofNodes-1}}}
    let .error (.budget exhausted) ← RootQuote.runWith action small
      | throwError "source identity accepted below its exact budget"
    unless exhausted.dimension == .proofNodes do throwError "wrong source identity budget exhausted"
    restored before sentinel (some names)
    logInfo m!"source identity exact/below budgets and success/failure rollback checked: {baseline.usage.proofNodes}"

    let negativeReader := q(ScalarPacket.read Data.rational Data.base.codec Data.native
      packet2.1 packet2.2.1 packet2.2.2)
    let .ok negative ← RootQuote.runWith (withParent fun context same decode =>
        ScalarPacket.quoteWith negativeReader context same decode) config
      | throwError "valid negative-conjugate enclosure packet refused"
    let factName := `Hex.RCF.SourceIdentityControls.negativeFact
    withExporting (isExporting := true) do
      addDecl (.defnDecl {
        name := factName,levelParams := [],
        type := ← inferType negative.value,value := negative.value,
        hints := .regular 0,safety := .safe}) (forceExpose := true)
      let readTarget ← mkEq negativeReader (← mkAppM ``Option.some #[mkConst factName])
      let readProof ← Hex.RCF.checkProof `negativePacket readTarget
        (mkExpectedPropHint negative.proof readTarget)
      addDecl (.thmDecl {
        name := `Hex.RCF.SourceIdentityControls.negative_read,
        levelParams := [],type := readTarget,value := readProof})
      let signTarget ← mkEq (← mkAppM ``Algebraic.SignFact.sign #[mkConst factName]) (toExpr (-1 : Int))
      let signProof ← Hex.RCF.checkProof `negativeSign signTarget
        (mkExpectedPropHint (← mkEqRefl (toExpr (-1 : Int))) signTarget)
      addDecl (.thmDecl {
        name := `Hex.RCF.SourceIdentityControls.negative_sign,
        levelParams := [],type := signTarget,value := signProof})
    let negativeValue : Q(ℝ) := q((Field.literalRep SquareTwo.polynomial negativeSquare
      negative_witness negative_precision).root.re)
    let negativeAnchor := {anchor with
      square := mkConst ``negativeSquare
      witness := mkConst ``negative_witness
      precision := mkConst ``negative_precision
      value := negativeValue
      selected := ← mkEqRefl negativeValue}
    let negativePackets := {packets with
      enclosure := negativeReader,enclosureValue := mkConst ``negative_value}
    let incorrect := {packets with equationValue := ← mkEqRefl (mkConst ``Bool.false)}
    for (label,a,p) in [("wrong conjugate",negativeAnchor,negativePackets),
        ("wrong coefficient proof",anchor,incorrect)] do
      let before ← getMCtx
      let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
      let refused ← try
          match ← RootQuote.runWith (do
            sentinel.mvarId!.assign (mkNatLit 97)
            quoteSource a p) config with
          | .ok _ => pure false
          | .error _ => pure true
        catch _ => pure true
      unless refused do throwError "source identity accepted {label}"
      restored before sentinel (some names)
      logInfo m!"source identity refused {label} with complete rollback"
end Hex.RCF.SourceIdentityControls
