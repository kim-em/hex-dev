/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients
public meta import HexRCF.RealCoefficients
public meta import Lean.Elab.Term
public meta import HexRCF.ProofEvidence
public section

namespace Hex.RCF.ReplayModes
open Lean Meta Qq

set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
set_option rcf.algebraic.singleReplay true
set_option rcf.algebraic.indexSigns false

theorem universal : ∀ x : ℝ,
    x ^ 2 - 2 * Real.sqrt 2 * x + 2 ≥ 0 := by rcf

theorem existential : ∃ x : ℝ,
    x ^ 2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 := by rcf

theorem guarded : ∀ x : ℝ,
    x / Real.sqrt 2 = (Real.sqrt 2 / 2) * x := by rcf

theorem bounded : ∃ x : ℝ, x ∈ Set.Ioc 1 2 ∧ x ^ 2 = Real.sqrt 2 := by rcf

set_option rcf.algebraic.singleReplay false in
theorem linear_split : ∃ x : ℝ,
    x ^ 2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 := by rcf

run_meta do
  for (name, route) in [(`Hex.RCF.ReplayModes.universal,
      ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkForall_sound),
      (`Hex.RCF.ReplayModes.existential,
        ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkExists_sound),
      (`Hex.RCF.ReplayModes.linear_split,
        ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkExists_sound)] do
    unless ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf route) do
      throwError "linear replay fixture {name} did not use its original soundness theorem"
    for indexed in [``Hex.RCF.RealCoefficients.FieldBuild.Result.checkForallIndex_eq,
        ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkExistsIndex_eq] do
      if ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf indexed) then
        throwError "linear replay fixture used indexed replay"

run_meta do
  for (target, expected) in #[
      (q(∀ x : ℝ, x ^ 2 + Real.sqrt 2 < 0),
        "rcf: the universal sentence is false"),
      (q(∀ x : ℝ, x ^ 2 + 0 / (Real.sqrt 2 - Real.sqrt 2) ≥ 0),
        "rcf: original closed divisor is zero")] do
    let saved ← saveState
    let error? ← try
      let _ ← Hex.RCF.proveGoal target
      pure none
    catch error => pure (some (← error.toMessageData.toString))
    saved.restore
    unless error?.any (·.startsWith expected) do
      throwError "unexpected replay-mode refusal: {error?}"

/-- info: 'Hex.RCF.ReplayModes.universal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms universal
/-- info: 'Hex.RCF.ReplayModes.existential' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms existential
/-- info: 'Hex.RCF.ReplayModes.guarded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms guarded
/-- info: 'Hex.RCF.ReplayModes.bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms bounded

/-- info: 'Hex.RCF.ReplayModes.linear_split' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms linear_split

end Hex.RCF.ReplayModes
