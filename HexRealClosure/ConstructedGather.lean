/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.ConstructedCatalog
public import HexRealClosure.ReconciledBase

public section
namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry}

/-- Every requested owner's provider keys, retaining their original order.
The native history constructor skips keys that are already present. -/
@[expose] def Live.Request.providerKeys (request : Live.Request registry) :
    List BaseContext.ConstantKey :=
  request.owners.flatMap fun owner => owner.origin.base.signature.constants

/-- Build and install a missing joint provider history, then use the ordinary
checked reconciliation factory for all requested live frames. The progress
reader is queried at each actual newly constructed predecessor. -/
def Live.Request.gatherConstructed? (request : Live.Request registry)
    (catalog : BaseContext.Catalog registry)
    (read : (parent : BaseContext.RealPrefix registry) → (key : BaseContext.ConstantKey) →
      Option (parent.Step key)) (parent : BaseContext.RealPrefix registry) :
    Option (Σ base, Live.Collection base request) := do
  let built ← catalog.construct? read parent request.providerKeys
  request.gatherReconciledFrom? built.next

/-- The final collection uses the exact newly returned catalog. -/
theorem Live.Request.gatherConstructed?_of_success (request : Live.Request registry)
    (catalog : BaseContext.Catalog registry)
    (read : (parent : BaseContext.RealPrefix registry) → (key : BaseContext.ConstantKey) →
      Option (parent.Step key)) (parent : BaseContext.RealPrefix registry)
    (packet : catalog.Construction read parent request.providerKeys)
    (constructed : catalog.construct? read parent request.providerKeys = some packet)
    (base : BaseContext.PackedContext registry) (collection : Live.Collection base request)
    (gathered : request.gatherReconciledFrom? packet.next = some ⟨base, collection⟩) :
    request.gatherConstructed? catalog read parent = some ⟨base, collection⟩ := by
  simp only [Live.Request.gatherConstructed?, constructed, bind, Option.bind, gathered]

/-- Acceptance retains the native construction packet and original factory
result, rather than replacing them with a compatible presentation. -/
theorem Live.Request.gatherConstructed?_gathered (request : Live.Request registry)
    (catalog : BaseContext.Catalog registry)
    (read : (parent : BaseContext.RealPrefix registry) → (key : BaseContext.ConstantKey) →
      Option (parent.Step key)) (parent : BaseContext.RealPrefix registry)
    (base : BaseContext.PackedContext registry) (collection : Live.Collection base request)
    (accepted : request.gatherConstructed? catalog read parent = some ⟨base, collection⟩) :
    ∃ packet : catalog.Construction read parent request.providerKeys,
      catalog.construct? read parent request.providerKeys = some packet ∧
        request.gatherReconciledFrom? packet.next = some ⟨base, collection⟩ := by
  unfold Live.Request.gatherConstructed? at accepted
  cases produced : catalog.construct? read parent request.providerKeys with
  | none => simp only [produced, bind, Option.bind, reduceCtorEq] at accepted
  | some packet =>
    simp only [produced, bind, Option.bind] at accepted
    exact ⟨packet, rfl, accepted⟩

end Hex.RealClosure.Tower
