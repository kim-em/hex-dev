/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.SelectedRoot.Frozen
public import Lean.Elab.Command

public section

meta section
namespace Hex.RCF.SelectedRootTests.FrozenCollect
open Hex.RCF.SelectedRootTests
open Lean Meta Elab Command Hex Hex.RealClosure Hex.SignDet
open Hex.RealClosure.Algebraic

private def control : TermElabM Unit := do
  let mut rules ← ReplayTools.rules
  for name in #[``Frozen.checkAt, ``RawDescriptor.check] do
    rules ← rules.addDeclToUnfold name
  rules ← rules.addConst ``Frozen.check_frozen
  let context ← Simp.mkContext (simpTheorems := #[rules])
    (congrTheorems := ← getSimpCongrTheorems)
  let program := mkConst ``Frozen.check
  let facts := mkConst ``Collect.facts
  let collected ← KernelReplay.collectMany 0 program #[⟨facts⟩] context (fun _ _ => pure none)
  match collected.outcome with
  | .checked true proof axioms =>
    let type ← mkEq (mkApp program facts) (mkConst ``Bool.true)
    let _ ← KernelReplay.auditProof proof type
    KernelCheck.addChecked `Hex.RCF.SelectedRootTests.FrozenCollect.accepted type proof
    logInfo m!"literal tree accepted: requests={collected.requests.size}, native unfolds=0, axioms={axioms}"
  | .checked false .. => throwError "literal descriptor rejected"
  | .missing application => throwError "missing frozen fact: {application}"

elab "#selected_frozen" : command => liftTermElabM control
end Hex.RCF.SelectedRootTests.FrozenCollect
/-- info: literal tree accepted: requests=0, native unfolds=0, axioms=[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
#selected_frozen
