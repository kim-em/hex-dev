/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.ConstructedGather
public import HexRealClosureTheory.BaseHistory
public import HexRealClosureTheory.ReconciledCatalog

public section
namespace Hex.RealClosure.BaseContext

/-- Installing the newly constructed model preserves every catalog model.
Only predecessor-relative validity of each actual read step is supplied. -/
theorem Catalog.Construction.models {registry : Registry} {catalog : Catalog registry}
    (models : catalog.Models)
    (read : (parent : RealPrefix registry) → (key : ConstantKey) → Option (parent.Step key))
    (parent : RealPrefix.Model registry) (keys : List ConstantKey)
    (valid : parent.Valid read keys)
    (packet : catalog.Construction read parent.context keys) : packet.next.Models := by
  rcases packet.inserted with unchanged | inserted
  · simpa only [unchanged] using models
  · obtain ⟨provider, same⟩ := parent.extend?_model read keys valid packet.built
    have installed : catalog.insert provider.context = some packet.next := by
      rw [same]
      exact inserted
    exact models.insert provider installed

/-- The actual constructed history has a staged realization at any requested
depth, derived from its own predecessor-relative provider premises. -/
theorem Catalog.Construction.realization {registry : Registry} {catalog : Catalog registry}
    (read : (parent : RealPrefix registry) → (key : ConstantKey) → Option (parent.Step key))
    (parent : RealPrefix.Model registry) (keys : List ConstantKey)
    (valid : parent.Valid read keys)
    (packet : catalog.Construction read parent.context keys) (depth : Nat) :
    Nonempty (packet.target.finish.extend depth).Realization := by
  obtain ⟨provider, same⟩ := parent.extend?_model read keys valid packet.built
  rw [← same]
  exact ⟨provider.staged depth⟩

end Hex.RealClosure.BaseContext

namespace Hex.RealClosure.Tower
variable {registry : BaseContext.Registry}

/-- Progress along the actual requested path and validity of its returned
steps suffice to gather every complete live frame at the constructed history.
No installed joint prefix, target realization or root agreement is supplied. -/
theorem Live.Request.gatherConstructed?_success (request : Live.Request registry)
    (catalog : BaseContext.Catalog registry)
    (read : (parent : BaseContext.RealPrefix registry) → (key : BaseContext.ConstantKey) →
      Option (parent.Step key))
    (parent : BaseContext.RealPrefix.Model registry)
    (valid : parent.Valid read request.providerKeys)
    (ready : BaseContext.RealPrefix.Ready read parent.context request.providerKeys)
    (distinct : ∀ owner ∈ request.owners, owner.origin.base.signature.constants.Nodup) :
    (request.gatherConstructed? catalog read parent.context).isSome = true := by
  have built := parent.extend?_success read request.providerKeys ready
  have install := catalog.construct?_success read parent.context request.providerKeys built
  obtain ⟨packet, constructed⟩ := Option.isSome_iff_exists.mp install
  obtain ⟨following⟩ := packet.realization read parent request.providerKeys valid
    (SharedBase.depth (request.owners.map (·.origin.base)))
  obtain ⟨collection, gathered, coherent⟩ := request.gatherReconciled?_models following
    following.reference.model (by
      intro owner member
      refine ⟨distinct owner member, ?_, ?_⟩
      · intro key included
        simp only [BaseContext.PackedContext.extend_signature,
          BaseContext.RealPrefix.finish_signature]
        apply packet.covers key
        exact Or.inr (List.mem_flatMap.mpr ⟨owner, member, included⟩)
      · simpa only [BaseContext.PackedContext.extend_signature,
          BaseContext.RealPrefix.finish_signature, BaseContext.PackedContext.depth, Nat.zero_add] using
          SharedBase.depth_bound (request.owners.map (·.origin.base)) owner.origin.base
            (List.mem_map.mpr ⟨owner, member, rfl⟩))
  rw [request.gatherConstructed?_of_success catalog read parent.context packet constructed
    collection gathered]
  rfl

/-- An accepted gather has the canonical shared model of its exact constructed
history. This is ambient-model semantics, not direct finite replay realization. -/
theorem Live.Request.gatherConstructed?_model (request : Live.Request registry)
    (catalog : BaseContext.Catalog registry)
    (read : (parent : BaseContext.RealPrefix registry) → (key : BaseContext.ConstantKey) →
      Option (parent.Step key))
    (parent : BaseContext.RealPrefix.Model registry)
    (valid : parent.Valid read request.providerKeys)
    (packet : catalog.Construction read parent.context request.providerKeys)
    (collection : Live.Collection (packet.target.finish.extend
      (SharedBase.depth (request.owners.map (·.origin.base)))) request)
    (accepted : request.gatherConstructed? catalog read parent.context = some ⟨packet, collection⟩) :
    ∃ following : (packet.target.finish.extend
        (SharedBase.depth (request.owners.map (·.origin.base)))).Realization,
      Nonempty (Shared.Model (reader := OwnerReader.reconciled following following.reference.model)
        collection.shared following following.reference.model) := by
  have gathered := (request.gatherConstructed?_gathered catalog read parent.context
    packet collection accepted).2
  obtain ⟨following⟩ := packet.realization read parent request.providerKeys valid
    (SharedBase.depth (request.owners.map (·.origin.base)))
  exact ⟨following, ⟨collection.reconciledModel following following.reference.model gathered⟩⟩

end Hex.RealClosure.Tower
