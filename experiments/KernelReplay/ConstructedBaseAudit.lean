/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRealClosureTheory.ConstructedCatalog
import KernelReplay.AxiomClosure

namespace Hex.RealClosure.Algebraic.KernelReplay.ConstructedBaseAudit
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
  let roots := #[``BaseContext.Catalog.Construction.realization,
    ``Tower.Live.Request.gatherConstructed?_gathered]
  let axioms ← AxiomClosure.collect roots
  let standard := #[`propext, `Classical.choice, `Quot.sound].qsort Name.lt
  unless axioms == standard do
    throwError "constructed base bridge changed its exact axiom closure"
  let forbidden := #[`Hex.RealClosure.BaseContext.PackedContext.Realization.reference,
    `Hex.RealClosure.Ambient.ofField, `Hex.RealClosure.Ambient.exists_ambient,
    `TauCeti.RealClosure.exists_realClosure]
  let environment := (← getEnv).checked.get
  let mut queue := roots
  let mut queued := roots.foldl (fun names name => names.insert name) ({} : NameSet)
  let mut cursor := 0
  while cursor < queue.size do
    Core.checkSystem "constructed base bridge full body audit"
    if ((← IO.getNumHeartbeats)-began)/1000 ≥ 1500000 then
      throwError "aggregate constructed base audit budget exhausted"
    if queue.size > 150000 then throwError "constructed base dependency bound exhausted"
    let name := queue[cursor]!
    cursor := cursor + 1
    if forbidden.contains name then
      throwError "constructed base binding retained a whole-field construction: {name}"
    let some info := environment.find? name |
      throwError "missing checked constructed base dependency: {name}"
    if info.isUnsafe || info.isPartial then
      throwError "unsafe constructed base dependency: {name}"
    for child in dependencies info do
      unless queued.contains child do
        queued := queued.insert child
        queue := queue.push child
  logInfo m!"constructed base bridge full body audit: roots=2 actualConstructedHistory=true acceptedGatherEquations=true axioms={axioms.toList} wholeFieldReferences=[] declarations={cursor} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.ConstructedBaseAudit
