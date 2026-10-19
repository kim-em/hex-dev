/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.SelectedRoot.Checks
import HexRCF.Tactic
import Lean.Elab.Command

open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.SelectedRootTests.Audit
open Hex.RCF.SelectedRootTests

private meta def primitives : Array Name := #[``Int.instNegInt, ``instOfNat, ``Codec.Json,
  ``instLTNat, ``Nat.decLt, ``List.instGetElemNatLtLength, ``List.length, ``instOfNatNat, ``id]

private meta partial def data (moduleIndex : ModuleIdx) (seen : NameHashSet)
    (name : Name) : MetaM NameHashSet := do
  if seen.contains name then return seen
  let mut seen := seen.insert name
  let info ← getConstInfo name
  let some body := info.value? (allowOpaque := true) |
    throwError "missing literal body {name}"
  for called in body.getUsedConstants do
    if (← getEnv).getModuleIdxFor? called == some moduleIndex then
      seen ← data moduleIndex seen called
    else
      let info ← getConstInfo called
      let harmless := primitives.contains called ||
        ((← getEnv).getProjectionFnInfo? called).isSome ||
        match info with
        | .ctorInfo _ | .inductInfo _ | .recInfo _ | .thmInfo _ => true
        | _ => false
      unless harmless do throwError "literal {name} calls unlisted computation {called}"
  return seen

/--
info: Hex.RCF.SelectedRootTests.Packets: 22 packets, complete literal definition closure checked
---
info: Hex.RCF.SelectedRootTests.Intermediates: 2 packets, complete literal definition closure checked
---
info: Hex.RCF.SelectedRootTests.RowIntermediates: 13 packets, complete literal definition closure checked
---
info: all fresh source and refusal proof axiom inventories checked
-/
#guard_msgs in
run_meta do
  for (names, count) in #[(`Hex.RCF.SelectedRootTests.Packets, 22), (`Hex.RCF.SelectedRootTests.Intermediates, 2),
      (`Hex.RCF.SelectedRootTests.RowIntermediates, 13)] do
    let first := Name.str names "packet0"
    let some index := (← getEnv).getModuleIdxFor? first | throwError "literal module missing"
    let mut seen : NameHashSet := {}
    for i in [:count] do
      seen ← data index seen (Name.str names s!"packet{i}")
    logInfo m!"{names}: {count} packets, complete literal definition closure checked"
  let names := #[``Literals.lowerSubject, ``Literals.lowerGraph,
    ``Literals.upperSubject, ``Literals.upperGraph, ``Literals.rowPacket]
  let some index := (← getEnv).getModuleIdxFor? names[0]! | throwError "source literals missing"
  let mut seen : NameHashSet := {}
  for name in names do seen ← data index seen name
  for name in #[``Proofs.exists_nested, ``Proofs.rowAccepted,
      ``Data.parent_eq, ``Data.alpha_value,
      ``Frozen.rawAccepted, ``Frozen.graphAccepted, ``Frozen.treeAccepted,
      ``FrozenCollect.accepted, ``Upper.rootAccepted, ``Upper.subjectRead,
      ``PacketFields.fields, ``SelectedFormula.checkRowWith_eq,
      ``SelectedFormula.row_domains, ``SelectedFormula.row_spec,
      ``SelectedFormula.row_sound, ``SelectedFormula.row_false,
      ``SelectedFormula.row_total, ``SelectedFormula.row_zero,
      ``Refusals.falseChecked, ``Refusals.coefficientChecked,
      ``Refusals.orderChecked, ``Refusals.rowChecked, ``Refusals.forgedTrueChecked,
      ``Checks.context_checked, ``Checks.negative_real,
      ``Checks.zero_real, ``Checks.falseAccepted, ``Checks.counterexample, ``Controls.zero_checked,
      ``Controls.sign_checked, ``Controls.version_checked] do
    Hex.RCF.checkAxioms name (mkConst name)
  logInfo "all fresh source and refusal proof axiom inventories checked"

end Hex.RCF.SelectedRootTests.Audit
