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
        ``FieldBuild.produce] do
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
  let before := (← getMCtx).mvarCounter
  let wrong ← observing? do
    prepared.transport (Lean.mkConst ``True.intro)
  unless wrong.isNone do throwError "transport accepted a proof of the wrong sentence"
  unless (← getMCtx).mvarCounter == before do
    throwError "failed transport leaked metavariables"
  let mismatched := {prepared with divisorIdentities := #[Lean.mkConst ``True.intro]}
  let invalidIdentity ← observing? mismatched.proveReplay
  unless invalidIdentity.isNone do throwError "incorrect original divisor identity was accepted"
  unless (← getMCtx).mvarCounter == before do
    throwError "failed divisor identity leaked metavariables"
  let missing := {prepared with divisorProofs := #[]}
  let rejected ← observing? missing.prove
  unless rejected.isNone do throwError "missing original divisor was accepted"
  unless (← getMCtx).mvarCounter == before do
    throwError "failed divisor preflight leaked metavariables"

run_meta do
  let rational : Q(Prop) := q(∀ x : ℝ, x ^ 2 ≥ 0)
  let zeroDivisor : Q(Prop) := q(∀ x : ℝ, x ^ 2 + 0 / (Real.sqrt 2 - Real.sqrt 2) ≥ 0)
  for (target, decline) in [(rational, true), (zeroDivisor, false)] do
    let before := (← getMCtx).mvarCounter
    let outcome ← observing? (Coefficients.prepare target)
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
  let rejected ← observing? prepared.proveReplay
  unless rejected.isNone do throwError "finite false verdict became a proof"
  unless (← getMCtx).mvarCounter == before do
    throwError "false finite verdict leaked metavariables"

end Hex.RCF.PreparedCoefficientsTests
