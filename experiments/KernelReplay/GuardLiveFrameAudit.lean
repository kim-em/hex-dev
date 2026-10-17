/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRealClosure.LiveFrame
import KernelReplay.GuardJoinPrefixAudit

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardLiveFrameAudit
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
  let roots := #[``Tower.Live.Collection.frame_transport,
    ``Tower.Live.Collection.frame_values, ``Tower.Live.Collection.frame_polynomials,
    ``Tower.Live.Collection.frame_descriptors]
  let axioms ← AxiomClosure.collect roots
  let standard := #[`propext, `Classical.choice, `Quot.sound].qsort Name.lt
  unless axioms == standard do
    throwError "native frame bindings changed their exact axiom closure"
  let forbidden := #[`Hex.RealClosure.BaseContext.PackedContext.Realization.reference,
    `Hex.RealClosure.Ambient.ofField, `Hex.RealClosure.Ambient.exists_ambient,
    `TauCeti.RealClosure.exists_realClosure]
  let environment := (← getEnv).checked.get
  let mut queue := roots
  let mut queued := roots.foldl (fun names name => names.insert name) ({} : NameSet)
  let mut cursor := 0
  while cursor < queue.size do
    Core.checkSystem "native source-frame binding full body audit"
    if ((← IO.getNumHeartbeats)-began)/1000 ≥ 1500000 then
      throwError "aggregate source-frame audit budget exhausted"
    if queue.size > 150000 then throwError "source-frame dependency bound exhausted"
    let name := queue[cursor]!
    cursor := cursor + 1
    if forbidden.contains name then
      throwError "source-frame binding retained a whole-field construction: {name}"
    let components := name.toString.splitOn "."
    if components.contains "Model" || components.contains "Models" ||
        components.contains "Mathlib" || components.any (·.endsWith "Theory") then
      throwError "source-frame binding retained a theory or model dependency: {name}"
    let some info := environment.find? name |
      throwError "missing checked source-frame dependency: {name}"
    if info.isUnsafe || info.isPartial then
      throwError "unsafe source-frame dependency: {name}"
    for child in dependencies info do
      unless queued.contains child do
        queued := queued.insert child
        queue := queue.push child
  logInfo m!"native source-frame binding full body audit: roots=4 originalRequestPositions=true sameRetainedInclusions=true fullRawDescriptors=true axioms={axioms.toList} wholeFieldReferences=[] theoryAndModelFree=true declarations={cursor} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardLiveFrameAudit
