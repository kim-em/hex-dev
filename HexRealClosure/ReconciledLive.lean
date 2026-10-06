/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.ReconciledGather
public import HexRealClosure.LiveRequest
import all HexRealClosure.LiveRequest

public section

namespace Hex.RealClosure.Tower.Live

variable {registry : BaseContext.Registry}

/-- Gather the complete owner ancestry through provider reconciliation, then
transport every requested operand and revalidate each descriptor in the one
returned target. The original request and checked maps remain available. -/
def Request.gatherReconciled? (base : BaseContext.PackedContext registry)
    (request : Request registry) : Option (Collection base request) := do
  let shared ← Shared.gatherReconciled? base request.owners
  match checked : request.transport? shared.maps with
  | none => none
  | some frames => return ⟨shared, frames, checked⟩

/-- Successful owner gathering and frame transport determine the actual live
collection, with no independently substituted target context. -/
theorem Request.gatherReconciled?_of_success (base : BaseContext.PackedContext registry)
    (request : Request registry) (shared : Shared base request.owners)
    (gathered : Shared.gatherReconciled? base request.owners = some shared)
    (frames : List (Frame shared.input.context))
    (checked : request.transport? shared.maps = some frames) :
    ∃ result, request.gatherReconciled? base = some result ∧ result.shared = shared := by
  refine ⟨⟨shared, frames, checked⟩, ?_, rfl⟩
  simp only [Request.gatherReconciled?, gathered, bind, Option.bind]
  split
  next failed => simp [checked] at failed
  next converted produced =>
    cases Option.some.inj (produced.symm.trans checked)
    rfl

/-- An accepted live collection retains the successful native owner gather. -/
theorem Request.gatherReconciled?_shared (base : BaseContext.PackedContext registry)
    (request : Request registry) (result : Collection base request)
    (produced : request.gatherReconciled? base = some result) :
    Shared.gatherReconciled? base request.owners = some result.shared := by
  unfold Request.gatherReconciled? at produced
  cases gathered : Shared.gatherReconciled? base request.owners with
  | none => simp [gathered] at produced
  | some shared =>
    simp only [gathered, bind, Option.bind] at produced
    split at produced
    next failed => simp at produced
    next converted checked =>
      cases Option.some.inj produced
      rfl

end Hex.RealClosure.Tower.Live

/-- info: 'Hex.RealClosure.Tower.Live.Request.gatherReconciled?_of_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Request.gatherReconciled?_of_success

/-- info: 'Hex.RealClosure.Tower.Live.Request.gatherReconciled?_shared' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Request.gatherReconciled?_shared
