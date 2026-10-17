/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.DependentQuoteData
public meta import HexRCF.DependentQuoteData
public meta import HexRCF.RealCoefficients.RootQuote
public section

/-! Checked dependent quotation and transactional refusal controls. -/

open Lean Meta Hex.RCF.RealCoefficients
namespace Hex.RCF.DependentQuote
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
private meta def refused (expected : String) (action : MetaM α) : MetaM Unit := do
  let rejected ← try
    let _ ← action
    pure false
  catch error =>
    if error.isInterrupt || error.isMaxHeartbeat || error.isMaxRecDepth then throw error
    unless (← error.toMessageData.toString).contains expected do throw error
    pure true
  unless rejected do throwError "expected terminal refusal containing {expected}"

run_meta do
  let decoder : RootQuote.DecoderM := fun expression => do
    if expression.isConstOf ``Hex.RCF.DependentQuote.gate then return some (mkConst ``Hex.RCF.DependentQuote.gate_eq)
    return none
  for name in [``Hex.RCF.DependentQuote.reader,``Hex.RCF.DependentQuote.nested] do
    let sentinel ← mkFreshExprMVar (mkConst ``Nat)
    let levelSentinel ← mkFreshLevelMVar
    let before ← getMCtx
    let mutateDecoder : RootQuote.DecoderM := fun expression => do
      if expression.isConstOf ``Hex.RCF.DependentQuote.gate then
        sentinel.mvarId!.assign (mkNatLit 99)
        let _ ← mkFreshExprMVar (mkConst ``Nat)
        assignLevelMVar levelSentinel.mvarId! .zero
        let _ ← mkFreshLevelMVar
      decoder expression
    let outcome ← RootQuote.runWith
      (RootQuote.quoteOptionWith (mkConst name) mutateDecoder)
    let .ok result := outcome | throwError "dependent reader quotation declined"
    let after ← getMCtx
    unless !(← sentinel.mvarId!.isAssigned) && before.mvarCounter == after.mvarCounter &&
        before.lmvarCounter == after.lmvarCounter &&
        before.eAssignment.toList == after.eAssignment.toList &&
        before.lAssignment.toList == after.lAssignment.toList &&
        before.decls.toList.map Prod.fst == after.decls.toList.map Prod.fst do
      throwError "dependent major retained caller metavariable changes"
    let config : Hex.RealFormula.Reify.Config := {}
    let exactBudget := {config with ring := {config.ring with budget :=
      {config.ring.budget with proofNodes := result.usage.proofNodes}}}
    let .ok exactResult ← RootQuote.runWith
        (RootQuote.quoteOptionWith (mkConst name) decoder) exactBudget
      | throwError "dependent major failed its exact proof budget"
    unless exactResult.usage.proofNodes == result.usage.proofNodes do
      throwError "dependent major has unstable resource accounting"
    let small := {config with ring := {config.ring with budget :=
      {config.ring.budget with proofNodes := result.usage.proofNodes-1}}}
    let .error (.budget exhausted) ← RootQuote.runWith
        (RootQuote.quoteOptionWith (mkConst name) decoder) small
      | throwError "dependent major did not exhaust one below its proof budget"
    unless exhausted.dimension == .proofNodes do
      throwError "dependent major exhausted a different resource"
    let statement ← mkEq (mkConst name) (← mkAppM ``Option.some #[result.value])
    let proof ← Hex.RCF.checkProof `majorProbe statement result.proof
    let axioms ← collectAxioms proof.getAppFn.constName!
    unless axioms.all (fun name => [``propext,``Classical.choice,``Quot.sound].contains name) do
      throwError "unexpected dependent-major axioms: {axioms}"
    logInfo m!"dependent major checked {name}; nodes={result.usage.proofNodes}; axioms={axioms}"
run_meta do
  let sentinel ← mkFreshExprMVar (mkConst ``Nat)
  let levelSentinel ← mkFreshLevelMVar
  let original ← getMCtx
  let marker := `Hex.RCF.DependentQuote.rollbackMarker
  let mutate := do
    sentinel.mvarId!.assign (mkNatLit 99)
    let _ ← mkFreshExprMVar (mkConst ``Nat)
    assignLevelMVar levelSentinel.mvarId! .zero
    let _ ← mkFreshLevelMVar
    let statement ← mkEq (mkNatLit 0) (mkNatLit 0)
    let proof ← mkEqRefl (mkNatLit 0)
    addDecl (.thmDecl {name := marker,levelParams := [],type := statement,value := proof})
  let unchanged := do
    let after ← getMCtx
    unless !(← sentinel.mvarId!.isAssigned) &&
        original.mvarCounter == after.mvarCounter &&
        original.lmvarCounter == after.lmvarCounter &&
        original.eAssignment.toList == after.eAssignment.toList &&
        original.lAssignment.toList == after.lAssignment.toList &&
        original.decls.toList.map Prod.fst == after.decls.toList.map Prod.fst &&
        !(← getEnv).contains marker do
      throwError "dependent refusal retained caller state"
  let decoder : RootQuote.DecoderM := fun expression => do
    if expression.isConstOf ``Hex.RCF.DependentQuote.gate then return some (mkConst ``Hex.RCF.DependentQuote.gate_eq)
    return none
  let .ok plain ← RootQuote.runWith
      (RootQuote.quoteOptionWith (mkConst ``Hex.RCF.DependentQuote.reader) decoder)
    | throwError "plain dependent quotation declined"
  let declined ← IO.mkRef false
  let .ok retry ← RootQuote.runWith
      (RootQuote.quoteOptionWith (mkConst ``Hex.RCF.DependentQuote.reader) fun expression => do
        if !expression.isConstOf ``Hex.RCF.DependentQuote.gate && !(← declined.get) then
          declined.set true
          mutate
          Hex.RealFormula.Reify.charge .proofNodes 7
          return none
        decoder expression)
    | throwError "a declined boundary changed dependent quotation"
  unless (← declined.get) && retry.usage.proofNodes == plain.usage.proofNodes+7 do
    throwError "dependent quotation discarded declined callback charges"
  unchanged
  refused "(kernel) application type mismatch" do
    RootQuote.runWith (RootQuote.quoteOptionWith (mkConst ``Hex.RCF.DependentQuote.reader)
      fun expression => do
        if expression.isConstOf ``Hex.RCF.DependentQuote.gate then
          mutate
          return some (← mkEqRefl (mkConst ``Bool.false))
        return none)
  unchanged
  let visits ← IO.mkRef 0
  refused "major provider failed" do
    RootQuote.runWith (RootQuote.quoteOptionWith (mkConst ``Hex.RCF.DependentQuote.reader)
      fun expression => do
        if expression.isConstOf ``Hex.RCF.DependentQuote.gate then
          visits.modify (·+1)
          mutate
          throwError "major provider failed"
        return none)
  unless (← visits.get) == 1 do throwError "terminal provider failure was retried"
  unchanged
  refused "literal Boolean replay remains" do
    RootQuote.runWith (RootQuote.quoteOptionWith (mkConst ``Hex.RCF.DependentQuote.reader)
      fun expression => do
        if expression.isConstOf ``Hex.RCF.DependentQuote.gate then mutate
        return none)
  unchanged
  refused "non-proof argument" do
    RootQuote.runWith (RootQuote.quoteOptionWith (mkConst ``Hex.RCF.DependentQuote.unsupported) decoder)
  unchanged
  logInfo "dependent major: charged decline, wrong proof, terminal failure, decline-only and non-proof trailing controls checked"
end Hex.RCF.DependentQuote
