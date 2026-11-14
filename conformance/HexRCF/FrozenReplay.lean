/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.CertificationInputs
public meta import HexRCF.CertificationInputs
public meta import HexRCF.RealCoefficients.CommonTactic
public meta import HexRCF.RealCoefficients.ReplayCells
public meta import Lean.Elab.Command
public section

open Hex Hex.RCF Hex.RCF.RealCoefficients Lean Meta Qq
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option debug.skipKernelTC false
set_option Elab.async false

run_meta do
  let target := q(∀ x : ℝ,
    x^2 + 1 / (Hex.RCF.CertificationInputs.realAlgebraic.toReal + Real.sqrt 2) > 0)
  let .ok prepared ← Coefficients.prepare target |
    throwError "frozen replay source preparation declined"
  unless prepared.polynomial.natDegree == 8 && prepared.divisors.length == 1 do
    throwError "expected a guarded common degree-eight source"
  let cert ← prepared.build
  let data := cert.data
  let input := prepared.input
  unless Replay.checkCells input cert == .ok true do
    throwError "valid frozen certificate rejected"
  let negative := {input with formula := .not input.formula}
  unless Replay.checkCells negative {cert with input := negative} == .ok false do
    throwError "valid false certificate lost its diagnostic verdict"
  let changed := {input with quantifier := .existsReal}
  unless Replay.checkCells changed cert == .error .binding do
    throwError "certificate accepted for a different quantified sentence"
  let changedValues := {input with values := fun _ => 0}
  unless Replay.checkCells changedValues cert == .error .binding do
    throwError "certificate accepted for different source coefficients"
  let missing := {data with signs := {data.signs with entries := []}}
  unless Replay.checkCells input {cert with data := missing} == .error .divisor do
    throwError "missing original divisor evidence bypassed preflight"
  let rows := {data.rootSigns with entries := []}
  unless Replay.checkCells input {cert with data := {data with rootSigns := rows}} ==
      .error .evidence do
    throwError "missing source-atom inventory accepted"
  let proof ← prepared.check cert
  let proof ← Hex.RCF.checkProof `Hex.RCF.FrozenReplay.original target proof
  addDecl (.thmDecl {
    name := `Hex.RCF.FrozenReplay.original
    levelParams := []
    type := target
    value := proof })
  let complete ← withOptions (fun options =>
    options.set `rcf.algebraic.directDepth (0 : Nat)) prepared.buildTotal
  unless Replay.checkCells prepared.input complete == .ok true do
    throwError "complete guarded degree-eight production failed frozen replay"
  let totalProof ← prepared.check complete
  let totalProof ← Hex.RCF.checkProof `Hex.RCF.FrozenReplay.total target totalProof
  addDecl (.thmDecl {
    name := `Hex.RCF.FrozenReplay.total
    levelParams := []
    type := target
    value := totalProof })
  let saved ← saveState
  let declarations := (← getEnv).constants.map₂.toList.length
  let rejected ← try
    let _ ← prepared.check {cert with data := missing}
    pure none
  catch error => pure (some (← error.toMessageData.toString))
  unless rejected.any (·.startsWith "rcf: prepared finite replay failed:") do
    throwError "unexpected malformed frozen replay result: {rejected}"
  unless (← getEnv).constants.map₂.toList.length == declarations do
    throwError "rejected frozen proof retained temporary declarations"
  saved.restore
  let falseTarget := q(∀ x : ℝ,
    x^2 + 1 / (Hex.RCF.CertificationInputs.realAlgebraic.toReal + Real.sqrt 2) < 0)
  let .ok falsePrepared ← Coefficients.prepare falseTarget |
    throwError "false source preparation declined"
  let completeFalse ← withOptions (fun options =>
    options.set `rcf.algebraic.directDepth (0 : Nat)) falsePrepared.buildTotal
  unless Replay.checkCells falsePrepared.input completeFalse == .ok false do
    throwError "complete false production did not return an accepted diagnostic certificate"
  for refinements in [0, 1] do
    let falseCert ← withOptions (fun options =>
        options.set `rcf.algebraic.signRefinements refinements) falsePrepared.build
    unless Replay.checkCells falsePrepared.input falseCert == .ok false do
      throwError "false build did not return an accepted diagnostic certificate"
    let saved ← saveState
    let declarations := (← getEnv).constants.map₂.toList.length
    let rejected ← try
      let _ ← falsePrepared.check falseCert
      pure none
    catch error => pure (some (← error.toMessageData.toString))
    unless rejected == some "rcf: the universal sentence is false on the prepared cells" do
      throwError "unexpected false frozen proof result: {rejected}"
    unless (← getEnv).constants.map₂.toList.length == declarations do
      throwError "false frozen proof retained temporary declarations"
    saved.restore
  logInfo "FROZEN_REPLAY: guarded degree-eight source; bounded/complete true and false production, bindings and malformed evidence checked; both original proofs checked"

/-- info: 'Hex.RCF.FrozenReplay.original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RCF.FrozenReplay.original

/-- info: 'Hex.RCF.FrozenReplay.total' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RCF.FrozenReplay.total
