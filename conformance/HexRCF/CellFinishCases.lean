/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellQuoteStages
open Lean Meta Qq Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.CellQuoteStages
namespace Hex.RCF.CellFinishCases
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

theorem zero_source : (∀ _x : ℝ, (0 : ℝ) = 0) ↔
    (∀ _x : ℝ, (0 : ℝ) / 0 = 0) := by simp

theorem cancelled_source : (∀ _x : ℝ, (0 : ℝ) = 0) ↔
    (∀ x : ℝ, (0 : ℝ) * (x / (Real.sqrt 2 - Real.sqrt 2)) = 0) := by simp

private meta def restored (before : MetavarContext) (sentinel : Expr)
    (names : Option (Array Name) := none) : MetaM Unit := do
  let after ← getMCtx
  unless !(← sentinel.mvarId!.isAssigned) && before.mvarCounter == after.mvarCounter &&
      before.lmvarCounter == after.lmvarCounter && before.eAssignment.toList == after.eAssignment.toList &&
      before.lAssignment.toList == after.lAssignment.toList &&
      before.decls.toList.map Prod.fst == after.decls.toList.map Prod.fst do
    throwError "cell finishing retained caller metavariables"
  if let some names := names then
    unless (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
      throwError "failed cell finishing retained declarations"

run_meta do
  withoutExporting do
    let target : Q(Prop) := q(∀ _x : ℝ, (0 : ℝ) = 0)
    let .ok source ← Reify.prepare target | throwError "finishing source was not reified"
    let program : Q(Except Replay.Error Bool) := q(CellOperations.check operations
      base.codec values (matrix true) [] cert .forallReal RootReplayLiterals.constant cells)
    let args := program.getAppArgs
    let info ← getFunInfoNArgs program.getAppFn args.size
    let inputs := args.zipIdx |>.filterMap fun (arg,i) =>
      if info.paramInfo[i]!.binderInfo.isExplicit then some arg else none
    let checker ← mkAppM ``CompleteReplay.check (inputs.extract 1 inputs.size)
    let same ← mkAppM ``CellOperations.check_eq inputs
    let strict ← mkAppM ``RootQuote.read_eq #[program,mkConst ``Bool.true,mkConst ``trueChecked]
    let accepted ← mkEqTrans (← mkEqSymm same) strict
    let model ← mkAppM ``NumberField.rationalModel #[mkConst ``registry]
    let valuation ← withLocalDeclD `i (← mkAppM ``Fin #[mkNatLit 0]) fun i => do
      mkLambdaFVars #[i] (← mkAppM ``Tower.Model.value #[model,mkApp (mkConst ``values) i])
    let identityType ← mkEq valuation source.valuation
    let hole ← mkFreshExprMVar identityType
    let remaining ← Lean.Elab.runTactic' hole.mvarId!
      (← `(tactic| funext i; exact Fin.elim0 i))
    unless remaining.isEmpty do throwError "empty finishing valuation left goals"
    let identity ← Hex.RCF.checkProof `finishingValuation identityType (← instantiateMVars hole)
    let sentinel ← mkFreshExprMVar (mkConst ``Nat)
    let before ← getMCtx
    let finish (source : Reify.Source) (goal : Expr) (proof : Expr := accepted) := do
      sentinel.mvarId!.assign (mkNatLit 98)
      CellQuote.finishPacketWith source goal checker proof model identity
    let basic : Hex.RealFormula.Reify.Config := {}
    let .ok baseline ← RootQuote.runWith (finish source target) basic source.usage
      | throwError "continued finishing baseline refused"
    restored before sentinel
    unless baseline.usage.proofNodes > source.usage.proofNodes &&
        baseline.usage.sourceNodes > source.usage.sourceNodes do
      throwError "finishing did not continue both source and proof accounting"
    let exact := {basic with ring := {basic.ring with budget :=
      {basic.ring.budget with proofNodes := baseline.usage.proofNodes}}}
    let .ok repeated ← RootQuote.runWith (finish source target) exact source.usage
      | throwError "finishing rejected its exact continued budget"
    unless repeated.usage == baseline.usage do throwError "continued finishing usage changed"
    restored before sentinel
    let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
    let small := {exact with ring := {exact.ring with budget :=
      {exact.ring.budget with proofNodes := baseline.usage.proofNodes-1}}}
    let .error (.budget exhausted) ← RootQuote.runWith (finish source target) small source.usage
      | throwError "finishing accepted below its cumulative proof budget"
    unless exhausted.dimension == .proofNodes do throwError "wrong finishing resource exhausted"
    restored before sentinel (some names)
    let noSource := {basic with ring := {basic.ring with budget :=
      {basic.ring.budget with sourceNodes := source.usage.sourceNodes}}}
    let .error (.budget exhausted) ← RootQuote.runWith (finish source target) noSource source.usage
      | throwError "finishing restarted its source budget"
    unless exhausted.dimension == .sourceNodes do throwError "wrong source resource exhausted"
    restored before sentinel (some names)
    for (label,prepared,goal,proof) in [
        ("target",source,q(∀ _x : ℝ, (0 : ℝ) = 1),accepted),
        ("divisor inventory",{source with divisors := #[q((1 : ℝ))]},target,accepted),
        ("equivalence",{source with proof := ← mkEqRefl (mkConst ``Bool.false)},target,accepted),
        ("verdict",source,target,← mkEqRefl (mkConst ``Bool.false))] do
      let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
      let refused ← try
          match ← RootQuote.runWith (finish prepared goal proof) basic source.usage with
          | .ok _ => pure false
          | .error _ => pure true
        catch _ => pure true
      unless refused do throwError "finishing accepted wrong {label}"
      restored before sentinel (some names)
    logInfo m!"continued cell finishing exact/below/source budgets, bindings and rollback checked: proofNodes={baseline.usage.proofNodes}; sourceNodes={baseline.usage.sourceNodes}"
    for (badTarget,equivalent) in #[
        (q(∀ _x : ℝ, (0 : ℝ) / 0 = 0),mkConst ``zero_source),
        (q(∀ x : ℝ, (0 : ℝ) * (x / (Real.sqrt 2 - Real.sqrt 2)) = 0),mkConst ``cancelled_source)] do
      let equivalent ← mkAppM ``Iff.trans #[source.proof,equivalent]
      let statement ← mkAppM ``Iff
        #[← mkAppM ``Hex.RealFormula.Prenex.toProp #[source.formula,source.valuation],badTarget]
      let equivalent ← Hex.RCF.checkProof `validZeroSource statement equivalent
      let hidden := {source with original := badTarget,proof := equivalent}
      let before ← getMCtx
      let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
      let refused ← try
          match ← RootQuote.runWith (finish hidden badTarget) basic source.usage with
          | .ok _ => pure false
          | .error _ => pure true
        catch _ => pure true
      unless refused do throwError "valid source equivalence hid an original zero divisor"
      restored before sentinel (some names)
    logInfo "prepared finishing refused zero/cancelled divisors despite valid source equivalences"
    let decode : RootQuote.DecoderM := fun expression => do
      if let some proof ← RowQuote.decoder expression then return some proof
      if let some proof ← SignatureQuote.decoder q(base.signature)
          (mkConst ``signatureData) (mkConst ``signature_literal) expression then
        return some proof
      liftM (RationalQuote.decoder (mkConst ``registry) expression)
    let declarations ← IO.mkRef 0
    let joint : Hex.RealFormula.Reify.ReifyM RootQuote.Result := do
      sentinel.mvarId!.assign (mkNatLit 99)
      let quoted ← CellQuote.replayWith program decode
      declarations.set (← (← getEnv).getLocalConstantInfos).size
      let strict ← mkAppM ``RootQuote.read_eq #[program,mkConst ``Bool.true,quoted.proof]
      let accepted ← mkEqTrans (← mkEqSymm same) strict
      CellQuote.finishPacketWith source target checker accepted model identity
    let before ← getMCtx
    let .ok complete ← RootQuote.runWith joint basic source.usage
      | throwError "joint cell quotation/source finishing refused"
    restored before sentinel
    let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
    declarations.set 0
    let late := {basic with ring := {basic.ring with budget :=
      {basic.ring.budget with proofNodes := complete.usage.proofNodes-1}}}
    let .error (.budget exhausted) ← RootQuote.runWith joint late source.usage
      | throwError "joint source attempt accepted below its complete budget"
    unless exhausted.dimension == .proofNodes && (← declarations.get) > names.size do
      throwError "joint exhaustion did not follow successful quotation with new declarations"
    restored before sentinel (some names)
    logInfo m!"joint late finishing exhaustion restored quotation declarations: limit={exhausted.limit}; consumed={exhausted.consumed}; requested={exhausted.requested}"
    let proof ← Hex.RCF.checkProof `jointCellSource target complete.proof
    withExporting (isExporting := true) do
      addDecl (.thmDecl {
        name := `Hex.RCF.CellFinishCases.source,levelParams := [],type := target,value := proof})
    let axioms ← collectAxioms `Hex.RCF.CellFinishCases.source
    unless axioms.all (fun name => [``propext,``Classical.choice,``Quot.sound].contains name) do
      throwError "joint cell finishing has inadmissible dependencies"
    logInfo m!"joint replay and original-source finishing proofNodes={complete.usage.proofNodes}; axioms={axioms}"
end Hex.RCF.CellFinishCases
