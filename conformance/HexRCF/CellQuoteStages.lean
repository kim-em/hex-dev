/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.NumberField
import HexRCF.RootReplayLiterals
import HexRCF.CellReplay.ZeroLiterals
import HexRCF.CellReplay.Literals
import HexRCF.RealCoefficients.CellQuote
import HexRCF.RealCoefficients.SignatureQuote
import HexRCF.RealCoefficients.RationalQuote
import HexRCF.RealCoefficients.RowQuote
open Lean Meta Qq Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.CellQuoteStages
def registry : BaseContext.Registry := fun _ => none
abbrev base := Hex.RealClosure.NumberField.base registry
abbrev signatureData : Codec.Json :=
  .array (.cons RootReplayLiterals.j0
    (.cons (.number 0) (.cons RootReplayLiterals.j0 .nil)))
theorem signature_literal : signatureData = base.signature.literal.toJson := by
  rw [Tower.Context.base_signature]
  unfold BaseContext.rational
  rw [BaseContext.Context.signature_real,BaseContext.RealContext.keys_rational]
  rfl
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
def operations : Hex.RealClosure.Replay.Operations base.sign :=
  ⟨inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,inferInstance,
    inferInstance,inferInstance,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,base.sign,rfl⟩
def values : Fin 0 → base.Value := Fin.elim0
def matrix (positive : Bool) : Hex.RealFormula.QF 1 :=
  .atom ⟨0,if positive then .eq else .gt⟩
def cert : RadicalCert base.Value Tower.Signature :=
  ⟨base.signature,1,1,1,0⟩
def cells : Codec.Json :=
  .array (.cons CellReplayTests.ZeroLiterals.sections
    (.cons CellReplayTests.ZeroLiterals.sectors .nil))
private meta def decode : RootQuote.DecoderM := fun expression => do
  if let some proof ← RowQuote.decoder expression then return some proof
  if let some proof ← SignatureQuote.decoder q(base.signature)
      (mkConst ``signatureData) (mkConst ``signature_literal) expression then
    return some proof
  liftM (RationalQuote.decoder (mkConst ``registry) expression)

private meta def restored (before : MetavarContext) (sentinel : Expr)
    (names : Option (Array Name) := none) : MetaM Unit := do
  let after ← getMCtx
  unless !(← sentinel.mvarId!.isAssigned) && before.mvarCounter == after.mvarCounter &&
      before.lmvarCounter == after.lmvarCounter && before.eAssignment.toList == after.eAssignment.toList &&
      before.lAssignment.toList == after.lAssignment.toList &&
      before.decls.toList.map Prod.fst == after.decls.toList.map Prod.fst do
    throwError "staged quotation retained caller metavariables"
  if let some names := names then
    unless (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
      throwError "rejected staged quotation retained declarations"

run_meta do
  withoutExporting do
    let basic : Hex.RealFormula.Reify.Config := {}
    let config := {basic with ring := {basic.ring with budget :=
      {basic.ring.budget with proofNodes := 2000000}}}
    for (positive,suffix) in [(true,`trueChecked),(false,`falseChecked)] do
      let flag : Q(Bool) := toExpr positive
      let program : Q(Except Replay.Error Bool) := q(CellOperations.check operations
        base.codec values (matrix $(flag)) [] cert .forallReal
        RootReplayLiterals.constant cells)
      let sentinel ← mkFreshExprMVar (mkConst ``Nat)
      let before ← getMCtx
      let action : Hex.RealFormula.Reify.ReifyM RootQuote.Result := do
        sentinel.mvarId!.assign (mkNatLit 91)
        CellQuote.replayWith program decode
      let .ok quoted ← RootQuote.runWith action config
        | throwError "staged zero reader refused {positive}"
      restored before sentinel
      let target ← mkEq (← mkAppM ``Except.toOption #[program])
        (← mkAppM ``Option.some #[toExpr positive])
      let proof ← Hex.RCF.checkProof `stagedZero target (mkExpectedPropHint quoted.proof target)
      withExporting (isExporting := true) do
        addDecl (.thmDecl {
          name := Name.append `Hex.RCF.CellQuoteStages suffix
          levelParams := []
          type := target
          value := proof})
      let axioms ← collectAxioms (Name.append `Hex.RCF.CellQuoteStages suffix)
      unless axioms.all (fun name => [``propext,``Classical.choice,``Quot.sound].contains name) do
        throwError "unexpected staged zero axioms"
      logInfo m!"staged zero {positive}: nodes={quoted.usage.proofNodes}; axioms={axioms}"
      if positive then
        let exact := {config with ring := {config.ring with budget :=
          {config.ring.budget with proofNodes := quoted.usage.proofNodes}}}
        let .ok repeated ← RootQuote.runWith action exact
          | throwError "staged quotation failed at its exact budget"
        unless repeated.usage == quoted.usage do throwError "staged quotation usage changed"
        restored before sentinel
        let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
        let small := {exact with ring := {exact.ring with budget :=
          {exact.ring.budget with proofNodes := quoted.usage.proofNodes-1}}}
        let .error (.budget exhausted) ← RootQuote.runWith action small
          | throwError "staged quotation accepted below its exact budget"
        unless exhausted.dimension == .proofNodes do throwError "wrong staged resource exhausted"
        restored before sentinel (some names)
        let touched ← IO.mkRef false
        let failed ← try
            let _ ← RootQuote.runWith (CellQuote.replayWith program fun _ => do
              touched.set true
              sentinel.mvarId!.assign (mkNatLit 92)
              return some (← mkEqRefl (mkConst ``Bool.false))) config
            pure false
          catch _ => pure true
        unless failed && (← touched.get) do
          throwError "staged quotation did not check the wrong-goal proposal"
        restored before sentinel (some names)
        logInfo "staged exact/below/wrong-goal and full caller restoration checked"

run_meta do
  withoutExporting do
    let program : Q(Except Replay.Error Bool) := q(CellOperations.check operations
      base.codec values (matrix true) [] cert .forallReal RootReplayLiterals.constant cells)
    let model ← mkAppM ``Hex.RealClosure.NumberField.rationalModel #[mkConst ``registry]
    let strict ← mkAppM ``RootQuote.read_eq #[program,mkConst ``Bool.true,mkConst ``trueChecked]
    let inputs := program.getAppArgs
    let info ← getFunInfoNArgs program.getAppFn inputs.size
    let inputs := inputs.zipIdx |>.filterMap fun (argument,index) =>
      if info.paramInfo[index]!.binderInfo.isExplicit then some argument else none
    let checker ← mkAppM ``CompleteReplay.check (inputs.extract 1 inputs.size)
    let same ← mkAppM ``CellOperations.check_eq inputs
    let accepted ← mkEqTrans (← mkEqSymm same) strict
    let target : Q(Prop) := q(∀ _x : ℝ, (0 : ℝ) = 0)
    let .ok source ← Reify.prepare target | throwError "constant original source was not reified"
    let valuation ← withLocalDeclD `i (← mkAppM ``Fin #[mkNatLit 0]) fun i => do
      let value ← mkAppM ``Tower.Model.value #[model,mkApp (mkConst ``values) i]
      mkLambdaFVars #[i] value
    let identityType ← mkEq valuation source.valuation
    let identity ← mkFreshExprMVar identityType
    let remaining ← Lean.Elab.runTactic' identity.mvarId!
      (← `(tactic| funext i; exact Fin.elim0 i))
    unless remaining.isEmpty do throwError "empty valuation identity left goals"
    let identity ← Hex.RCF.checkProof `stagedValuation identityType (← instantiateMVars identity)
    let proof ← CellQuote.finishPacket target checker accepted model identity
    withExporting (isExporting := true) do
      addDecl (.thmDecl {
        name := `Hex.RCF.CellQuoteStages.source
        levelParams := []
        type := target
        value := proof})
    let falseProgram : Q(Except Replay.Error Bool) := q(CellOperations.check operations
      base.codec values (matrix false) [] cert .forallReal RootReplayLiterals.constant cells)
    let falseStrict ← mkAppM ``RootQuote.read_eq
      #[falseProgram,mkConst ``Bool.false,mkConst ``falseChecked]
    let falseInputs := inputs.set! 3 q(matrix false)
    let falseChecker ← mkAppM ``CompleteReplay.check (falseInputs.extract 1 falseInputs.size)
    let falseSame ← mkAppM ``CellOperations.check_eq falseInputs
    let falseAccepted ← mkEqTrans (← mkEqSymm falseSame) falseStrict
    let sentinel ← mkFreshExprMVar (mkConst ``Nat)
    let before ← getMCtx
    let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
    let failed ← try
        let _ ← CellQuote.finishPacket target falseChecker falseAccepted model identity
        pure false
      catch _ => pure true
    unless failed do throwError "false staged verdict proved the original goal"
    restored before sentinel (some names)
    logInfo "staged replay proves its original constant source; false verdict cannot prove that source"

run_meta do
  withoutExporting do
    let basic : Hex.RealFormula.Reify.Config := {}
    let config := {basic with ring := {basic.ring with budget :=
      {basic.ring.budget with proofNodes := 2000000}}}
    let malformed : Q(Except Replay.Error Bool) := q(CellOperations.check operations
      base.codec values (matrix true) [] cert .forallReal RootReplayLiterals.constant (.array .nil))
    let guarded : Q(Except Replay.Error Bool) := q(CellOperations.check operations
      base.codec values (matrix true) [0] cert .forallReal .null .null)
    let sentinel ← mkFreshExprMVar (mkConst ``Nat)
    let before ← getMCtx
    for (program,label) in [(malformed,"cells"),(guarded,"zero guard")] do
      let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
      let graph ← IO.mkRef false
      let .error (.providerFailure (.invalidProviderEvidence ..) _) ← RootQuote.runWith (do
          sentinel.mvarId!.assign (mkNatLit 93)
          CellQuote.replayWith program fun expression => do
            if expression.getAppFn.isConstOf ``Codec.readGraph then graph.set true
            decode expression) config
        | throwError "invalid staged {label} accepted"
      if label == "zero guard" && (← graph.get) then
        throwError "original zero guard did not precede graph decoding"
      restored before sentinel (some names)
    let program : Q(Except Replay.Error Bool) := q(CellOperations.check operations
      base.codec values (matrix true) [] cert .forallReal RootReplayLiterals.constant cells)
    let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
    let .error (.providerFailure (.invalidProviderEvidence ⟨key,version⟩ _) _) ←
        RootQuote.runWith (CellQuote.replayWith program fun _ => do
          sentinel.mvarId!.assign (mkNatLit 94)
          Hex.RealFormula.Reify.abort (.providerFailure (.invalidProviderEvidence
            ⟨`Hex.RCF.CellQuoteStages,7⟩ "synthetic provider failure") #[])) config
      | throwError "staged callback failure was not terminal"
    unless key == `Hex.RCF.CellQuoteStages && version == 7 do
      throwError "staged callback changed its structured failure"
    restored before sentinel (some names)
    logInfo "staged malformed cells, original zero guard, terminal callback and full rollback checked"
namespace Quadratic
def polynomial : base.Poly := DensePoly.ofCoeffs #[-2,0,1]
def atom : Hex.RealFormula.Poly 1 := MvPoly.X 0 ^ 2 - 2
def matrix : Hex.RealFormula.QF 1 := .and (.atom ⟨atom,.ge⟩)
  (.and (.atom ⟨atom,.le⟩) (.atom ⟨0,.eq⟩))
def cert : RadicalCert base.Value Tower.Signature :=
  ⟨base.signature,polynomial,polynomial,polynomial,1⟩
def cells : Codec.Json := .array (.cons CellReplayTests.Literals.sections
  (.cons CellReplayTests.Literals.sectors .nil))
set_option maxHeartbeats 24000000 in
set_option trace.Hex.RCF.CellQuote true in
run_meta do
  withoutExporting do
    let basic : Hex.RealFormula.Reify.Config := {}
    let config := {basic with ring := {basic.ring with budget :=
      {basic.ring.budget with proofNodes := 16000000}}}
    for (quantifier,verdict,suffix) in
        [(Hex.RealFormula.Quantifier.existsReal,true,`existsChecked)] do
      let quantifier : Q(Hex.RealFormula.Quantifier) := match quantifier with
        | .existsReal => q(Hex.RealFormula.Quantifier.existsReal)
        | .forallReal => q(Hex.RealFormula.Quantifier.forallReal)
      let program : Q(Except Replay.Error Bool) := q(CellOperations.check operations
        base.codec values matrix [] cert $(quantifier) RootReplayLiterals.whole cells)
      let quoted ← match ← RootQuote.runWith (CellQuote.replayWith program decode) config with
        | .ok quoted => pure quoted
        | .error error => throwError "staged quadratic reader refused {verdict}: {Hex.RealFormula.Reify.Error.toMessageData error}"
      let target ← mkEq (← mkAppM ``Except.toOption #[program])
        (← mkAppM ``Option.some #[toExpr verdict])
      let proof ← Hex.RCF.checkProof `stagedQuadratic target
        (mkExpectedPropHint quoted.proof target)
      withExporting (isExporting := true) do
        addDecl (.thmDecl {
          name := Name.append `Hex.RCF.CellQuoteStages.Quadratic suffix
          levelParams := [],type := target,value := proof})
      logInfo m!"staged two-root quadratic {verdict}: nodes={quoted.usage.proofNodes}"
end Quadratic
end Hex.RCF.CellQuoteStages
