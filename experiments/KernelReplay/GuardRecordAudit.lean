/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardRecordReplay
public import KernelReplay.GuardRecordStore
public import KernelReplay.GuardNativeAudit

public section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRecordAudit
open Lean Meta Elab Command FiniteData

private def bounded (began : Nat) : MetaM Nat := do
  Core.checkSystem "public native inventory full body audit"
  let used := ((← IO.getNumHeartbeats)-began)/1000
  if used ≥ 1500000 then throwError "aggregate inventory audit budget exhausted"
  return 1500000-used

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
  let roots := GuardRecordStore.roots.getState (← getEnv)
  unless !roots.isEmpty do throwError "native inventory audit roots are missing"
  let packingCount : Nat := 23
  let signCount : Nat := 12
  let unaffectedCount : Nat := 4
  let mut results : Array Expr := #[]
  for (kind, count) in #[("packing", packingCount), ("valueSign", signCount)] do
    for index in [:count] do
      let name := `Hex.RealClosure.Algebraic.KernelReplay.GuardRecordReplay ++
        Name.mkSimple s!"{kind}{index}"
      let info ← getConstInfo name
      unless info.isDefinition && info.levelParams.isEmpty do
        throwError "native inventory public record {name} is missing"
      unless roots.contains name do throwError "public record {name} was omitted from the audit roots"
      results := results.push (mkConst name)
  let axioms ← AxiomClosure.collect roots
  unless axioms == (#[`propext, `Classical.choice, `Quot.sound].qsort Name.lt) do
    throwError "replayed native inventory changed checked-body axiom closure"
  let fullEnvironment ← getEnv
  let checked := fullEnvironment.checked.get
  let initial := roots.foldl (fun found name => found.insert name) ({} : NameSet)
  let mut auditQueue := initial.toArray
  let mut auditQueued := initial
  let mut auditParents : NameMap Name := {}
  let mut auditCursor := 0
  while auditCursor < auditQueue.size do
    let _ ← bounded began
    if auditQueue.size > 150000 then throwError "replayed inventory dependency bound exhausted"
    let name := auditQueue[auditCursor]!
    auditCursor := auditCursor + 1
    if (`Real).isPrefixOf name ||
        (`Hex.RealClosure.Algebraic.KernelReplay.FiniteData.NativeModels).isPrefixOf name ||
        (`Hex.RealClosure.BaseContext.PackedContext.Realization).isPrefixOf name then
      throwError "replayed native inventory retained semantic dependency {name}"
    if let some index := fullEnvironment.getModuleIdxFor? name then
      let moduleName := fullEnvironment.header.moduleNames[index.toNat]!
      if moduleName.toString.startsWith "Mathlib." ||
          (moduleName.toString.splitOn "Theory").length > 1 then
        let mut path := #[name]
        let mut current := name
        for _ in [:64] do
          let some parent := auditParents.find? current | break
          path := path.push parent
          current := parent
        throwError "replayed native inventory retained companion dependency {name} from {moduleName}; reversePath={path}"
    let some info := checked.find? name | throwError "missing replayed native inventory checked body"
    if info.isUnsafe || info.isPartial then throwError "unsafe replayed native inventory dependency"
    for dependency in dependencies info do
      unless auditQueued.contains dependency do
        auditQueued := auditQueued.insert dependency
        auditParents := auditParents.insert dependency name
        auditQueue := auditQueue.push dependency
  logInfo m!"native inventory replay result: packings={packingCount} cachedSigns={signCount} storedSourceBindings={packingCount + signCount} unaffectedAlsoReplayed={unaffectedCount} totalRecords={results.size} axioms={axioms} mathlibModules=[] companionModules=[] modelNamespaces=[] declarations={auditCursor} aggregateHeartbeat={((← IO.getNumHeartbeats) - began) / 1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardRecordAudit
