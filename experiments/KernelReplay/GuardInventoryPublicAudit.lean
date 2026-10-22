/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardInventoryPublic
public import KernelReplay.GuardInventoryAudit

public section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardInventoryPublicAudit
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
  let roots := #[``GuardInventoryPublic.first_data, ``GuardInventoryPublic.first_conditions]
  let axioms ← AxiomClosure.collect roots
  unless axioms == (#[`propext, `Classical.choice, `Quot.sound].qsort Name.lt) do
    throwError "public record consumers changed their complete axiom closure"
  let forbidden := #[`Hex.RealClosure.BaseContext.PackedContext.Realization.reference,
    `Hex.RealClosure.Ambient.ofField, `Hex.RealClosure.Ambient.exists_ambient,
    `TauCeti.RealClosure.exists_realClosure]
  let environment := (← getEnv).checked.get
  let mut queue := roots
  let mut queued := roots.foldl (fun names name => names.insert name) ({} : NameSet)
  let mut cursor := 0
  while cursor < queue.size do
    Core.checkSystem "public record consumer full body audit"
    if ((← IO.getNumHeartbeats)-began)/1000 ≥ 1500000 then
      throwError "aggregate public record audit budget exhausted"
    if queue.size > 150000 then throwError "public record audit dependency bound exhausted"
    let name := queue[cursor]!
    cursor := cursor + 1
    if forbidden.contains name then throwError "public consumer retained whole-field construction {name}"
    let some info := environment.find? name | throwError "missing checked public consumer body {name}"
    if info.isUnsafe || info.isPartial then throwError "unsafe public consumer dependency {name}"
    for child in dependencies info do
      unless queued.contains child do
        queued := queued.insert child
        queue := queue.push child
  logInfo m!"public finite inventory consumer audit: roots=2 ordinaryPublicImports=true exactStandardAxioms=true wholeFieldReferences=[] declarations={cursor} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardInventoryPublicAudit
