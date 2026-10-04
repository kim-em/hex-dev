/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public meta import HexRCF.RealCoefficients
public meta import Lean
public meta import HexRCF.ProofEvidence
public section

namespace Hex.RCF.PreparedCoefficientsTests
open Hex RealCoefficients Lean Meta Qq
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000

-- Observe the API's own rollback, including runtime failures. Do not let the
-- test's exception observer backtrack on its behalf.
private meta def attempt (action : MetaM α) : MetaM (Option α) :=
  tryCatchRuntimeEx (some <$> action) (fun _ => pure none)

elab "prepared_probe" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target ← goal.getType
  let .ok prepared ← Coefficients.prepare target |
    throwError "exact-field preparation did not recognize the source"
  let proof ← prepared.prove
  goal.assign proof
  Lean.Elab.Tactic.replaceMainGoal []

elab "finite_probe" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let .ok prepared ← Coefficients.prepare (← goal.getType) |
    throwError "finite replay preparation did not recognize the source"
  let proof ← prepared.proveReplay
  goal.assign proof
  Lean.Elab.Tactic.replaceMainGoal []

elab "total_probe" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let .ok prepared ← Coefficients.prepare (← goal.getType) |
    throwError "total replay preparation did not recognize the source"
  let proof ← prepared.proveTotalReplay
  goal.assign proof
  Lean.Elab.Tactic.replaceMainGoal []

-- Force the complete producer past its direct bounded proposal. The ordinary
-- kernel proof still contains only replay, not the erased progress/search code.
set_option rcf.algebraic.directDepth 0 in
theorem total_domain : ∃ x ∈ Set.Ioc (1 : ℝ) 2, x ^ 2 = Real.sqrt 2 := by total_probe

theorem total_guarded : ∀ x : ℝ,
    x / Real.sqrt 2 = (Real.sqrt 2 / 2) * x := by total_probe

/-- info: 'Hex.RCF.PreparedCoefficientsTests.total_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms total_domain
/-- info: 'Hex.RCF.PreparedCoefficientsTests.total_guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms total_guarded

theorem finite_guarded : ∀ x : ℝ, x ^ 2 + 1 / (Real.sqrt 2 + 1) > 0 := by finite_probe

theorem finite_domain : ∃ x ∈ Set.Ioc (1 : ℝ) 2, x ^ 2 = Real.sqrt 2 := by finite_probe

/-- info: 'Hex.RCF.PreparedCoefficientsTests.finite_guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finite_guarded
/-- info: 'Hex.RCF.PreparedCoefficientsTests.finite_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finite_domain

theorem finite_cancelled : ∀ x : ℝ, x ^ 2 + 0 / (Real.sqrt 2 + 1) ≥ 0 := by finite_probe

theorem finite_empty : ∀ x ∈ Set.Ioc (2 : ℝ) 1, x ^ 2 + Real.sqrt 2 < 0 := by finite_probe

/-- info: 'Hex.RCF.PreparedCoefficientsTests.finite_cancelled' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finite_cancelled
/-- info: 'Hex.RCF.PreparedCoefficientsTests.finite_empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms finite_empty

run_meta do
  for name in [`Hex.RCF.PreparedCoefficientsTests.finite_guarded,
      `Hex.RCF.PreparedCoefficientsTests.finite_domain,
      `Hex.RCF.PreparedCoefficientsTests.finite_cancelled,
      `Hex.RCF.PreparedCoefficientsTests.finite_empty,
      `Hex.RCF.PreparedCoefficientsTests.total_domain,
      `Hex.RCF.PreparedCoefficientsTests.total_guarded] do
    unless ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf ``Replay.check_sound) do
      throwError "prepared finite proof did not use the public replay checker"
    for forbidden in [``Replay.build, ``Replay.buildTotal, ``FieldBuild.produceWithin,
        ``FieldBuild.produce, ``Field.prepareSign, ``Sturm.queryPrepared,
        ``Sturm.certifyPrepared, ``FieldBuild.buildTable] do
      if ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf forbidden) then
        throwError "prepared finite quotation embedded a producer"

theorem guarded : ∀ x : ℝ, x ^ 2 + 1 / (Real.sqrt 2 + 1) > 0 := by prepared_probe

theorem independent : ∀ x : ℝ, x ^ 2 + Real.sqrt 2 + Real.sqrt 3 > 0 := by prepared_probe

theorem domain : ∃ x ∈ Set.Ioc (1 : ℝ) 2, x ^ 2 = Real.sqrt 2 := by prepared_probe

/-- info: 'Hex.RCF.PreparedCoefficientsTests.guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms guarded
/-- info: 'Hex.RCF.PreparedCoefficientsTests.independent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms independent
/-- info: 'Hex.RCF.PreparedCoefficientsTests.domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms domain

run_meta do
  let target : Q(Prop) := q(∀ x : ℝ, x ^ 2 + 1 / (Real.sqrt 2 + 1) > 0)
  let .ok prepared ← Coefficients.prepare target | throwError "guarded preparation failed"
  unless prepared.divisorProofs.size == 1 do
    throwError "preparation lost an original divisor"
  -- The result type agrees, but the unused argument is ill typed. Public
  -- guard preflight must check this even when its caller disables kernel TC.
  let malformed := mkApp
    (mkLambda `unused .default (mkConst ``False) prepared.divisorProofs[0]!)
    (mkConst ``True.intro)
  let invalid := {prepared with divisorProofs := #[malformed]}
  let before := (← getMCtx).mvarCounter
  let invalidGuard ← withOptions (debug.skipKernelTC.set · true) do
    attempt invalid.checkDomains
  unless invalidGuard.isNone do throwError "direct guard preflight skipped kernel checking"
  unless (← getMCtx).mvarCounter == before do
    throwError "failed direct guard preflight leaked metavariables"
  let scalar : Q(ℝ) ← mkFreshExprMVar q(ℝ)
  let unresolved ← mkFreshExprMVar q($scalar ≠ 0)
  let unbound := {prepared with divisorProofs := #[unresolved]}
  let failed ← attempt unbound.checkDomains
  unless failed.isNone do throwError "direct guard preflight accepted an unresolved proof"
  unless (← scalar.mvarId!.isAssigned) == false do
    throwError "failed direct guard preflight leaked a unification assignment"
  let before := (← getMCtx).mvarCounter
  let wrong ← attempt do
    prepared.transport (Lean.mkConst ``True.intro)
  unless wrong.isNone do throwError "transport accepted a proof of the wrong sentence"
  unless (← getMCtx).mvarCounter == before do
    throwError "failed transport leaked metavariables"
  let mismatched := {prepared with divisorIdentities := #[Lean.mkConst ``True.intro]}
  let invalidIdentity ← attempt mismatched.proveReplay
  unless invalidIdentity.isNone do throwError "incorrect original divisor identity was accepted"
  unless (← getMCtx).mvarCounter == before do
    throwError "failed divisor identity leaked metavariables"
  let missing := {prepared with divisorProofs := #[]}
  let rejected ← attempt missing.prove
  unless rejected.isNone do throwError "missing original divisor was accepted"
  unless (← getMCtx).mvarCounter == before do
    throwError "failed divisor preflight leaked metavariables"

run_meta do
  let rational : Q(Prop) := q(∀ x : ℝ, x ^ 2 ≥ 0)
  let zeroDivisor : Q(Prop) := q(∀ x : ℝ, x ^ 2 + 0 / (Real.sqrt 2 - Real.sqrt 2) ≥ 0)
  for (target, decline) in [(rational, true), (zeroDivisor, false)] do
    let before := (← getMCtx).mvarCounter
    let outcome ← attempt (Coefficients.prepare target)
    if decline then
      match outcome with
      | some (.error (.unsupported _ _)) => pure ()
      | _ => throwError "rational preparation did not return a structured decline"
    else
      unless outcome.isNone do throwError "zero-divisor preparation did not fail"
    unless (← getMCtx).mvarCounter == before do
      throwError "unsuccessful preparation leaked metavariables"

run_meta do
  let target : Q(Prop) := q(∀ x : ℝ, x ^ 2 = Real.sqrt 2)
  let .ok prepared ← Coefficients.prepare target | throwError "false-sentence preparation failed"
  let before := (← getMCtx).mvarCounter
  let rejected ← attempt prepared.proveReplay
  unless rejected.isNone do throwError "finite false verdict became a proof"
  unless (← getMCtx).mvarCounter == before do
    throwError "false finite verdict leaked metavariables"

-- Assigned metavariables cannot hide nonstandard proof dependencies. These
-- synthetic terms are rejected in meta code and never become theorem proofs.
run_meta do
  let target : Q(Prop) := q(∀ x : ℝ, x ^ 2 + 1 / (Real.sqrt 2 + 1) > 0)
  let .ok prepared ← Coefficients.prepare target | throwError "guarded preparation failed"
  let guardType ← inferType prepared.divisorProofs[0]!
  let assigned ← mkFreshExprMVar guardType
  assigned.mvarId!.assign (← mkSorry guardType false)
  let invalid := {prepared with divisorProofs := #[assigned]}
  let rejected ← attempt invalid.checkDomains
  unless rejected.isNone do throwError "assigned guard proof hid a forbidden dependency"

run_meta do
  let target : Q(Prop) := q(∀ x : ℝ, x ^ 2 + 1 / (Real.sqrt 2 + 1) > 0)
  let .ok prepared ← Coefficients.prepare target | throwError "guarded preparation failed"
  let equality ← inferType prepared.valuationProof
  let fixedType ← mkAppM ``RealFormula.Prenex.toProp
    #[prepared.source.formula, equality.getAppArgs[1]!]
  for hidden in [false, true] do
    let forbidden ← mkSorry fixedType false
    let proposed ← if hidden then do
        let assigned ← mkFreshExprMVar fixedType
        assigned.mvarId!.assign forbidden
        pure assigned
      else pure forbidden
    let rejected ← attempt (prepared.transport proposed)
    unless rejected.isNone do throwError "transport accepted a forbidden proof dependency"

run_meta do
  let target : Q(Prop) := q(∀ x : ℝ, x ^ 2 + 1 / (Real.sqrt 2 + 1) > 0)
  let .ok prepared ← Coefficients.prepare target | throwError "guarded preparation failed"
  let missing := {prepared with
    source.divisors := #[]
    divisorProofs := #[]
    divisors := []
    divisorExpressions := #[]
    divisorIdentities := #[]}
  let rejected ← attempt missing.checkDomains
  unless rejected.isNone do throwError "editable source silently dropped an original guard"

-- Successful preparation and transport retain closed proof declarations but
-- preserve caller metavariables. Unresolved proof types cannot be unified away.
run_meta do
  let target : Q(Prop) := q(∀ x : ℝ, x ^ 2 + 1 / (Real.sqrt 2 + 1) > 0)
  let before := (← getMCtx).mvarCounter
  let .ok prepared ← Coefficients.prepare target | throwError "guarded preparation failed"
  unless (← getMCtx).mvarCounter == before do
    throwError "successful preparation leaked temporary metavariables"
  let congr ← withLocalDeclD `ρ (← inferType prepared.source.valuation) fun ρ => do
    let body ← mkAppM ``RealFormula.Prenex.toProp #[prepared.source.formula, ρ]
    mkAppM ``congrArg #[← mkLambdaFVars #[ρ] body, prepared.valuationProof]
  let specialized ← mkAppM ``Iff.mpr #[prepared.source.proof, mkConst ``guarded]
  let fixed ← mkAppM ``Eq.mpr #[congr, specialized]
  let unknown ← mkFreshExprMVar (mkSort .zero)
  let unresolved := mkApp2 (mkConst ``id [.zero]) unknown fixed
  let before := (← getMCtx).mvarCounter
  let rejected ← attempt (prepared.transport unresolved)
  unless rejected.isNone do throwError "transport unified an unresolved caller proof type"
  if ← unknown.mvarId!.isAssigned then throwError "transport assigned a caller proof type"
  unless (← getMCtx).mvarCounter == before do
    throwError "unresolved transport leaked temporary metavariables"
  let proof ← prepared.transport fixed
  unless (← getMCtx).mvarCounter == before do
    throwError "successful transport leaked temporary metavariables"
  if proof.hasMVar then throwError "successful transport returned temporary metavariables"
  Hex.RCF.checkAxioms `Hex.RCF.PreparedCoefficientsTests proof
  checkWithKernel proof

-- Runtime diagnostics must refer to the exact prepared source, even when a
-- caller edits the public record. Validate before either producer starts.
run_meta do
  let target : Q(Prop) := q(∃ x ∈ Set.Ioc (1 : ℝ) 2, x ^ 2 = Real.sqrt 2)
  let .ok prepared ← Coefficients.prepare target | throwError "binding fixture failed"
  let invalid := [( {prepared with quantifier := .forallReal},
      "rcf: invalid prepared sentence binding"),
    ({prepared with formula := .not prepared.formula},
      "rcf: invalid prepared sentence binding"),
    ({prepared with values := fun _ => 0},
      "rcf: invalid prepared coefficient binding")]
  for (candidate, expected) in invalid do
    for mode in [0, 1, 2] do
      let before := (← getMCtx).mvarCounter
      let failure ← tryCatchRuntimeEx (do
        let _ ← match mode with
          | 0 => candidate.prove
          | 1 => candidate.proveReplay
          | _ => candidate.proveTotalReplay
        pure none) (fun error => do pure (some (← error.toMessageData.toString)))
      unless failure == some expected do
        throwError "edited prepared input reported the wrong diagnostic: {failure}"
      unless (← getMCtx).mvarCounter == before do
        throwError "invalid prepared binding leaked metavariables"

-- Editing both runtime and expression syntax still cannot replace the source
-- equivalence with a proof of a different sentence before a false diagnostic.
run_meta do
  let target : Q(Prop) := q(∃ x ∈ Set.Ioc (1 : ℝ) 2, x ^ 2 = Real.sqrt 2)
  let .ok prepared ← Coefficients.prepare target | throwError "source fixture failed"
  let matrix := mkApp (mkConst ``RealFormula.QF.ff) (mkNatLit (prepared.arity + 1))
  let formula ← mkAppM ``RealFormula.Prenex.matrix #[matrix]
  let sentence ← mkAppM ``RealFormula.Prenex.quant
    #[mkConst ``RealFormula.Quantifier.existsReal, formula]
  let invalid := {prepared with
    formula := .ff
    formulaExpr := matrix
    source.formula := sentence}
  for mode in [false, true] do
    let before := (← getMCtx).mvarCounter
    let failure ← tryCatchRuntimeEx (do
      let _ ← if mode then invalid.proveTotalReplay else invalid.proveReplay
      pure none) (fun error => do pure (some (← error.toMessageData.toString)))
    unless failure.isSome && failure != some "rcf: the prepared finite sentence is false" do
      throwError "edited source equivalence became a false verdict"
    unless (← getMCtx).mvarCounter == before do
      throwError "invalid source equivalence leaked metavariables"

-- Validation-only proof checks leave no unreferenced auxiliary declarations.
run_meta do
  let target : Q(Prop) := q(∀ x : ℝ, x ^ 2 + 1 / (Real.sqrt 2 + 1) > 0)
  let .ok prepared ← Coefficients.prepare target | throwError "guard fixture failed"
  let before := (← getEnv).constants.map₂.toList.length
  prepared.checkDomains
  unless (← getEnv).constants.map₂.toList.length == before do
    throwError "domain validation retained unused theorem declarations"
  let invalid := {prepared with divisors := [0]}
  let failure ← tryCatchRuntimeEx (do
    let _ ← invalid.proveReplay
    pure none) (fun error => do pure (some (← error.toMessageData.toString)))
  unless failure == some "rcf: invalid prepared divisor binding" do
    throwError "edited divisor reported the wrong diagnostic: {failure}"

end Hex.RCF.PreparedCoefficientsTests
