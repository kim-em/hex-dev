/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.SelectedRoot.Controls
import HexRCF.SelectedRoot.RowCollect
import HexRealClosureTheory.KernelReplay
import Lean.Elab.Command

meta section
namespace Hex.RCF.SelectedRootTests.Refusals
open Hex.RCF.SelectedRootTests
open Lean Meta Elab Command Hex.RealClosure.Algebraic

private def control : TermElabM Unit := do
  let rules ← RowTools.rules
  let context ← Simp.mkContext (simpTheorems := #[rules])
    (congrTheorems := ← getSimpCongrTheorems)
  let incomplete ← KernelReplay.collectMany 0 (mkConst ``Row.rowProgram)
    #[⟨mkConst ``Collect.facts⟩] context (fun _ _ => pure none)
  match incomplete.outcome with
  | .missing application =>
    let needed ← KernelReplay.request application
    unless ← isDefEq needed.context (mkConst ``Data.native) do
      throwError "incomplete row reached a different field"
    unless incomplete.requests.size == 1 do throwError "missing request was not retained"
    logInfo "missing intermediates remain unresolved, without a Boolean verdict"
  | .checked .. => throwError "incomplete arithmetic inventory gave a verdict"
  for (programName, theoremName) in #[
      (``Controls.falseProgram, `Hex.RCF.SelectedRootTests.Refusals.falseChecked),
      (``Controls.wrongCoefficient, `Hex.RCF.SelectedRootTests.Refusals.coefficientChecked),
      (``Controls.swappedKeys, `Hex.RCF.SelectedRootTests.Refusals.orderChecked),
      (``Controls.forgedRow, `Hex.RCF.SelectedRootTests.Refusals.rowChecked),
      (``Controls.forgedTrue, `Hex.RCF.SelectedRootTests.Refusals.forgedTrueChecked)] do
    let program := mkConst programName
    let facts := mkConst ``RowCollect.facts
    let collected ← KernelReplay.collectMany 0 program #[⟨facts⟩] context (fun _ _ => pure none)
    match collected.outcome with
    | .checked true proof axioms =>
      let type ← mkEq (mkApp program facts) (mkConst ``Bool.true)
      let _ ← KernelReplay.auditProof proof type
      KernelCheck.addChecked theoremName type proof
      logInfo m!"{programName}: true; requests={collected.requests.size}; native unfolds=0; axioms={axioms}"
    | .checked false .. => throwError "{programName} failed its exact expected result"
    | .missing application => throwError "{programName} needs an unrecorded fact: {application}"

elab "#selected_refusals" : command => liftTermElabM control
end Hex.RCF.SelectedRootTests.Refusals
/--
info: missing intermediates remain unresolved, without a Boolean verdict
---
info: Hex.RCF.SelectedRootTests.Controls.falseProgram: true; requests=0; native unfolds=0; axioms=[propext, Classical.choice, Quot.sound]
---
info: Hex.RCF.SelectedRootTests.Controls.wrongCoefficient: true; requests=0; native unfolds=0; axioms=[propext, Classical.choice, Quot.sound]
---
info: Hex.RCF.SelectedRootTests.Controls.swappedKeys: true; requests=0; native unfolds=0; axioms=[propext, Classical.choice, Quot.sound]
---
info: Hex.RCF.SelectedRootTests.Controls.forgedRow: true; requests=0; native unfolds=0; axioms=[propext, Classical.choice, Quot.sound]
---
info: Hex.RCF.SelectedRootTests.Controls.forgedTrue: true; requests=0; native unfolds=0; axioms=[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
#selected_refusals

/-- info: 'Hex.RCF.SelectedRootTests.Refusals.falseChecked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RCF.SelectedRootTests.Refusals.falseChecked
/-- info: 'Hex.RCF.SelectedRootTests.Refusals.coefficientChecked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RCF.SelectedRootTests.Refusals.coefficientChecked
/-- info: 'Hex.RCF.SelectedRootTests.Refusals.orderChecked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RCF.SelectedRootTests.Refusals.orderChecked

/-- info: 'Hex.RCF.SelectedRootTests.Refusals.rowChecked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RCF.SelectedRootTests.Refusals.rowChecked

/-- info: 'Hex.RCF.SelectedRootTests.Refusals.forgedTrueChecked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RCF.SelectedRootTests.Refusals.forgedTrueChecked
