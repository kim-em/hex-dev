/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardNativeBindings

public section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardNativeAudit
open Lean Meta Elab

private def dependencies (info : ConstantInfo) : Array Name :=
  match info with
  | .axiomInfo info => info.type.getUsedConstants
  | .defnInfo info => info.type.getUsedConstants ++ info.value.getUsedConstants
  | .thmInfo info => info.type.getUsedConstants ++ info.value.getUsedConstants
  | .opaqueInfo info => info.type.getUsedConstants ++ info.value.getUsedConstants
  | .ctorInfo info => info.type.getUsedConstants
  | .recInfo info => info.type.getUsedConstants
  | .inductInfo info => info.type.getUsedConstants ++ info.ctors.toArray
  | .quotInfo _ => #[]


set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let environment ← getEnv
  let checked := environment.checked.get
  let roots := checked.constants.fold (fun found name info =>
    if name.toString.startsWith "_private.KernelReplay.GuardNativeFrontier." &&
        info.type.getAppFn.isConstOf ``SignFact then found.push name else found) (#[] : Array Name)
  unless roots.size == 17 do throwError "audit lost rebuilt source sign records"
  let mut sources : NameSet := {}
  for root in roots do
    let source ← origin root
    let .thmInfo certificate ← getConstInfo (root.appendAfter "_binding") |
      throwError "missing stored binding proof"
    let remaining := 1500000 - (((← IO.getNumHeartbeats) - began) / 1000)
    withOptions (maxHeartbeats.set · remaining) do
      kernelCheck `__recheckOriginalBinding certificate.type certificate.value
    sources := sources.insert source
  unless sources.size == 17 do throwError "rebuilt records do not bind seventeen distinct sources"
  let axioms ← AxiomClosure.collect roots
  unless axioms == (#[`propext, `Classical.choice, `Quot.sound].qsort Name.lt) do
    throwError "rebuilt source record audit changed axiom closure"
  let mut queue := roots
  let mut queued := roots.foldl (fun found name => found.insert name) ({} : NameSet)
  let mut cursor := 0
  while cursor < queue.size do
    Core.checkSystem "rebuilt sign record module audit"
    if ((← IO.getNumHeartbeats) - began) / 1000 ≥ 1500000 then
      throwError "aggregate rebuilt record audit budget exhausted"
    if queue.size > 150000 then throwError "rebuilt record audit graph bound exhausted"
    let name := queue[cursor]!
    cursor := cursor + 1
    if (`Real).isPrefixOf name ||
        (`Hex.RealClosure.Algebraic.KernelReplay.FiniteData.NativeModels).isPrefixOf name ||
        (`Hex.RealClosure.BaseContext.PackedContext.Realization).isPrefixOf name then
      throwError "rebuilt sign record retained semantic declaration {name}"
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := environment.header.moduleNames[index.toNat]!
      if moduleName.toString.startsWith "Mathlib." ||
          (moduleName.toString.splitOn "Theory").length > 1 then
        throwError "rebuilt sign record retained companion declaration {name} from {moduleName}"
    let some info := checked.find? name | throwError "missing complete checked body {name}"
    if info.isUnsafe || info.isPartial then throwError "unsafe/partial rebuilt record dependency {name}"
    for dependency in dependencies info do
      unless queued.contains dependency do
        queued := queued.insert dependency
        queue := queue.push dependency
  logInfo m!"rebuilt source record module audit: roots={roots.size} declarations={cursor} axioms={axioms} mathlibModules=[] companionModules=[] semanticNamespaces=[]"
  let forbidden := #[`Hex.RealClosure.BaseContext.PackedContext.Realization.reference,
    `Hex.RealClosure.Ambient.ofField, `Hex.RealClosure.Ambient.exists_ambient,
    `TauCeti.RealClosure.exists_realClosure]
  let mut cutQueue := #[``GuardCapture.second.data]
  let mut cutQueued : NameSet := ({} : NameSet).insert ``GuardCapture.second.data
  let mut cutCursor := 0
  while cutCursor < cutQueue.size do
    Core.checkSystem "original inventory source cut"
    if ((← IO.getNumHeartbeats) - began) / 1000 ≥ 1500000 then
      throwError "aggregate source binding audit budget exhausted"
    if cutQueue.size > 150000 then throwError "original source cut graph bound exhausted"
    let name := cutQueue[cutCursor]!
    cutCursor := cutCursor + 1
    if forbidden.contains name then throwError "stored source cut retained whole-field reference {name}"
    if sources.contains name then continue
    let some info := checked.find? name | throwError "missing original source cut declaration"
    for dependency in dependencies info do
      unless cutQueued.contains dependency do
        cutQueued := cutQueued.insert dependency
        cutQueue := cutQueue.push dependency
  logInfo m!"stored source binding audit: distinctSources={sources.size} recheckedBindings={roots.size} sourceCutDeclarations={cutCursor} remainingWholeFieldReferences=[]"

end Hex.RealClosure.Algebraic.KernelReplay.GuardNativeAudit
