/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.SelectedRoot.PackingMissing
import HexRCF.Tactic

open Lean Meta Hex Hex.RealClosure Hex.SignDet
open Hex.RCF.SelectedRootTests

namespace Hex.RCF.SelectedRootTests.PackingAudit
/-- Signed integer literals, the natural packet count and the JSON type alias.
No list indexing or arbitrary identity helper is permitted in constructor data. -/
private meta def primitives : Array Name := #[``Int.instNegInt, ``instOfNat,
  ``instOfNatNat, ``Codec.Json]

private meta partial def data (moduleIndex : ModuleIdx) (seen : NameHashSet)
    (name : Name) : MetaM NameHashSet := do
  if seen.contains name then return seen
  let mut seen := seen.insert name
  let info ← getConstInfo name
  let some body := info.value? (allowOpaque := true) | throwError "missing literal body {name}"
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
info: 43 packing packets: exact 1322-definition literal closure checked
---
info: actual original-packing row proof body passed active kernel producer diagnostics
-/
#guard_msgs in
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
run_meta do
  let some index := (← getEnv).getModuleIdxFor? `Hex.RCF.SelectedRootTests.PackingData.packet0
    | throwError "literal module missing"
  let mut seen : NameHashSet := {}
  for i in [:PackingData.count] do
    seen ← data index seen (Name.str `Hex.RCF.SelectedRootTests.PackingData s!"packet{i}")
  seen ← data index seen ``PackingData.count
  unless seen.size == 1322 do throwError "literal declaration count changed: {seen.size}"
  logInfo m!"43 packing packets: exact {seen.size}-definition literal closure checked"
  for name in #[``Hex.RCF.SelectedRootTests.PackingReplay.valueZero, ``Hex.RCF.SelectedRootTests.PackingReplay.vanished, ``Hex.RCF.SelectedRootTests.PackingReplay.storedZero,
      ``Hex.RCF.SelectedRootTests.PackingReplay.accepted, ``Hex.RCF.SelectedRootTests.PackingReplay.exists_nested,
      ``Hex.RCF.SelectedRootTests.Packing.evaluate_eq, ``Hex.RCF.SelectedRootTests.Packing.checked,
      ``Hex.RCF.SelectedRootTests.Packing.source] do
    Hex.RCF.checkAxioms name (mkConst name)
  for i in [:PackingData.count] do
    let name := Name.str `Hex.RCF.SelectedRootTests.PackingReplay s!"read{i}"
    Hex.RCF.checkAxioms name (mkConst name)
    let .thmInfo link ← getConstInfo name | throwError "missing stable packet-record law"
    KernelCheck.addChecked (← mkFreshUserName `__originalPackingReadBody) link.type link.value
  let .thmInfo info ← getConstInfo ``Hex.RCF.SelectedRootTests.PackingReplay.accepted
    | throwError "missing actual acceptance proof body"
  KernelCheck.addChecked (← mkFreshUserName `__originalPackingBody) info.type info.value
  logInfo "actual original-packing row proof body passed active kernel producer diagnostics"
end Hex.RCF.SelectedRootTests.PackingAudit
