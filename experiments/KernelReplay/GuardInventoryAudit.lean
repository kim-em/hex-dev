/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import KernelReplay.GuardInventoryReplay
import KernelReplay.GuardRecordAudit

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardInventoryAudit
open Lean Meta Elab FiniteData

private def bounded (began : Nat) : MetaM Nat := do
  Core.checkSystem "module first inventory full body audit"
  let used := ((← IO.getNumHeartbeats)-began)/1000
  if used ≥ 1500000 then throwError "aggregate first inventory audit budget exhausted"
  return 1500000-used

private def stage (began : Nat) (message : String) : MetaM Unit := do
  let _ ← bounded began
  logInfo m!"{message} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

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
  let existence := mkConst ``GuardInventoryReplay.baseExists
  let data := mkConst ``GuardInventoryReplay.firstData
  let firstSpec := mkConst ``GuardInventoryReplay.firstSpec
  let roots := #[existence, data, firstSpec].flatMap Expr.getUsedConstants
  let axioms ← AxiomClosure.collect roots
  unless axioms == (#[`propext, `Classical.choice, `Quot.sound].qsort Name.lt) do
    throwError "reconstructed first prefix changed axiom closure"
  let forbidden := #[`Hex.RealClosure.BaseContext.PackedContext.Realization.reference,
    `Hex.RealClosure.Ambient.ofField, `Hex.RealClosure.Ambient.exists_ambient,
    `TauCeti.RealClosure.exists_realClosure]
  let environment := (← getEnv).checked.get
  let initial := roots.foldl (fun found name => found.insert name) ({} : NameSet)
  let mut queue := initial.toArray
  let mut queued := initial
  let mut cursor := 0
  while cursor < queue.size do
    let _ ← bounded began
    if queue.size > 150000 then throwError "reconstructed prefix dependency bound exhausted"
    let name := queue[cursor]!
    cursor := cursor + 1
    if forbidden.contains name then throwError "reconstructed first prefix retained whole-field construction {name}"
    let some info := environment.find? name | throwError "missing reconstructed prefix checked body {name}"
    if info.isUnsafe || info.isPartial then throwError "unsafe reconstructed prefix dependency {name}"
    for dependency in dependencies info do
      unless queued.contains dependency do
        queued := queued.insert dependency
        queue := queue.push dependency
  stage began s!"first prefix axiom and whole-field dependency audits passed; declarations={cursor}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardInventoryAudit
