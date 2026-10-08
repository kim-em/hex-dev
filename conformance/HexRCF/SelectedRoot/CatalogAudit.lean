/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.SelectedRoot.Catalog
public import HexRCF.SelectedRoot.CatalogBytes
public import HexRCF.SelectedRoot.CatalogControls
public import HexRCF.SelectedRoot.KernelCheck
public import HexRealClosureMathlib.KernelReplay
public import Lean.Elab.Command

public section

open Hex Hex.RealClosure Hex.RCF.SelectedRootTests
meta section
namespace Hex.RCF.SelectedRootTests.CatalogAudit
open Lean Meta Elab Command
private partial def data (moduleIndex : ModuleIdx) (seen : NameHashSet)
    (name : Name) (allowed : Array Name) : MetaM NameHashSet := do
  if seen.contains name then return seen
  let mut seen := seen.insert name
  let info ← getConstInfo name
  let some body := info.value? (allowOpaque := true) | throwError "missing literal body {name}"
  for called in body.getUsedConstants do
    if (← getEnv).getModuleIdxFor? called == some moduleIndex then
      seen ← data moduleIndex seen called allowed
    else
      let info ← getConstInfo called
      let harmless := allowed.contains called ||
        ((← getEnv).getProjectionFnInfo? called).isSome ||
        match info with
        | .ctorInfo _ | .inductInfo _ | .recInfo _ | .thmInfo _ => true
        | _ => false
      unless harmless do throwError "literal {name} calls unlisted computation {called}"
  return seen

elab "#catalog_audit" : command => liftTermElabM do
  for (root, expected, allowed) in #[
      (``Hex.RCF.SelectedRootTests.CatalogData.packet, 75,
        #[``Int.instNegInt, ``instOfNat, ``instOfNatNat, ``Hex.SignDet.Codec.Json]),
      (``Hex.RCF.SelectedRootTests.CatalogByteData.literal, 21, #[``UInt8.ofNat, ``UInt8.instOfNat])] do
    let some index := (← getEnv).getModuleIdxFor? root | throwError "missing literal module"
    let checked ← data index {} root allowed
    unless checked.size == expected do
      throwError "literal closure count {root}: {checked.size}, expected {expected}"
    for (name, info) in (← getEnv).constants do
      if (← getEnv).getModuleIdxFor? name == some index then
        if let .defnInfo _ := info then
          unless checked.contains name do throwError "unchecked literal definition {name}"
    logInfo m!"complete literal closure {root}: {checked.size} definitions"
  for name in #[``Hex.RCF.SelectedRootTests.CatalogSource.fresh,
      ``Hex.RCF.SelectedRootTests.CatalogSource.source, ``Hex.RCF.SelectedRootTests.CatalogPacket.treeLeaf, ``Hex.RCF.SelectedRootTests.CatalogPacket.frame,
      ``Hex.RCF.SelectedRootTests.CatalogPacket.written, ``Hex.RCF.SelectedRootTests.CatalogPacket.decoded,
      ``Hex.RCF.SelectedRootTests.CatalogPacket.accepted, ``Hex.RCF.SelectedRootTests.CatalogPacket.supplied,
      ``Hex.RCF.SelectedRootTests.CatalogBytes.packetWritten, ``Hex.RCF.SelectedRootTests.CatalogBytes.written,
      ``Hex.RCF.SelectedRootTests.CatalogBytes.bound, ``Hex.RCF.SelectedRootTests.CatalogBytes.accepted,
      ``Hex.RCF.SelectedRootTests.CatalogBytes.source, ``Hex.RCF.SelectedRootTests.CatalogBytes.exists_nested,
      ``Hex.RCF.SelectedRootTests.CatalogControls.truncatedCheck] do
    let info ← getConstInfo name
    let some value := info.value? (allowOpaque := true) | throwError "missing body {name}"
    let axioms ← Algebraic.KernelReplay.auditProof value info.type
    KernelCheck.addChecked (← mkFreshUserName `__catalog) info.type value
    logInfo m!"guarded catalog body {name}: {axioms}"
  -- Check the two new base-transport helpers, including their private bodies.
  let some sourceIndex := (← getEnv).getModuleIdxFor?
    ``Hex.RCF.SelectedRootTests.CatalogSource.fresh | throwError "missing source module"
  let mut helpers := 0
  for (name, info) in (← getEnv).constants do
    if (← getEnv).getModuleIdxFor? name == some sourceIndex then
      if name.toString.endsWith ".originBase" || name.toString.endsWith ".castBase" then
        let some value := info.value? (allowOpaque := true) | throwError "missing transport body"
        let axioms ← Algebraic.KernelReplay.auditProof value info.type
        if name.toString.endsWith ".originBase" then
          KernelCheck.addChecked (← mkFreshUserName `__catalogBase) info.type value
        else
          Algebraic.KernelReplay.kernelCheck (← mkFreshUserName `__catalogCast) info.type value
        helpers := helpers + 1
        logInfo m!"checked source transport {name}: {axioms}"
  unless helpers == 2 do throwError "missing source transport helpers"
  for name in #[``Hex.RCF.SelectedRootTests.CatalogSource.denote,
      ``Hex.RCF.SelectedRootTests.CatalogBytes.size, ``Hex.RCF.SelectedRootTests.CatalogControls.staleBinding,
      ``Hex.RCF.SelectedRootTests.CatalogControls.staleRejected, ``Hex.RCF.SelectedRootTests.CatalogControls.setRejected,
      ``Hex.RCF.SelectedRootTests.CatalogControls.byteLimit, ``Hex.RCF.SelectedRootTests.CatalogControls.byteLimitRejected,
      ``Hex.RCF.SelectedRootTests.CatalogControls.truncatedRejected] do
    let info ← getConstInfo name
    let some value := info.value? (allowOpaque := true) | throwError "missing control body"
    let axioms ← Algebraic.KernelReplay.auditProof value info.type
    Algebraic.KernelReplay.kernelCheck (← mkFreshUserName `__catalogControl) info.type value
    logInfo m!"ordinary control body {name}: {axioms}"
end Hex.RCF.SelectedRootTests.CatalogAudit
end
set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
#catalog_audit
