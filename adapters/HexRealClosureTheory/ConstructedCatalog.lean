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
    (valid : ∀ (parent : RealPrefix.Model registry) (key : ConstantKey)
      (step : parent.context.Step key), read parent.context key = some step →
        parent.StepCorrect key step)
    (parent : RealPrefix.Model registry) (keys : List ConstantKey)
    (packet : catalog.Construction read parent.context keys) : packet.next.Models := by
  obtain ⟨provider, same⟩ := parent.extend?_model read valid keys packet.built
  have inserted : catalog.insert provider.context = some packet.next := by
    rw [same]
    exact packet.inserted
  exact models.insert provider inserted

end Hex.RealClosure.BaseContext

namespace Hex.RealClosure.Tower
variable {registry : BaseContext.Registry}

/-- Build a missing joint history from relative provider premises and gather
every complete live frame. The requested keys come from those actual owners;
no installed joint prefix, target realization or root agreement is an input. -/
theorem Live.Request.gatherConstructed?_success (request : Live.Request registry)
    (catalog : BaseContext.Catalog registry) (models : catalog.Models)
    (read : (parent : BaseContext.RealPrefix registry) → (key : BaseContext.ConstantKey) →
      Option (parent.Step key))
    (valid : ∀ (parent : BaseContext.RealPrefix.Model registry) (key : BaseContext.ConstantKey)
      (step : parent.context.Step key), read parent.context key = some step →
        parent.StepCorrect key step)
    (parent : BaseContext.RealPrefix.Model registry)
    (ready : ∀ (current : BaseContext.RealPrefix.Model registry) (key : BaseContext.ConstantKey),
      key ∈ request.providerKeys → key ∉ current.context.keys →
        (read current.context key).isSome = true)
    (missing : ∀ target, BaseContext.RealPrefix.extend? read parent.context request.providerKeys =
      some target → catalog.lookup target.keys = none)
    (distinct : ∀ owner ∈ request.owners, owner.origin.base.signature.constants.Nodup) :
    (request.gatherConstructed? catalog read parent.context).isSome = true := by
  have built := parent.extend?_success read valid request.providerKeys ready
  have install := catalog.construct?_success read parent.context request.providerKeys built missing
  obtain ⟨packet, constructed⟩ := Option.isSome_iff_exists.mp install
  have nextModels := packet.models models read valid parent request.providerKeys
  have success := request.gatherReconciledFrom?_success nextModels packet.target packet.installed (by
    intro owner member
    refine ⟨distinct owner member, ?_⟩
    intro key included
    apply packet.covers key
    apply Or.inr
    exact List.mem_flatMap.mpr ⟨owner, member, included⟩)
  obtain ⟨⟨base, collection⟩, gathered⟩ := Option.isSome_iff_exists.mp success
  rw [request.gatherConstructed?_of_success catalog read parent.context packet constructed
    base collection gathered]
  rfl

/-- An accepted constructed gather has the ordinary canonical shared model of
its actual returned native collection. Every source interpretation is derived
from the newly constructed provider history through the existing reconciliation
proofs. This is ambient-model semantics, not direct finite replay realization. -/
theorem Live.Request.gatherConstructed?_model (request : Live.Request registry)
    (catalog : BaseContext.Catalog registry) (models : catalog.Models)
    (read : (parent : BaseContext.RealPrefix registry) → (key : BaseContext.ConstantKey) →
      Option (parent.Step key))
    (valid : ∀ (parent : BaseContext.RealPrefix.Model registry) (key : BaseContext.ConstantKey)
      (step : parent.context.Step key), read parent.context key = some step →
        parent.StepCorrect key step)
    (parent : BaseContext.RealPrefix.Model registry)
    (base : BaseContext.PackedContext registry) (collection : Live.Collection base request)
    (accepted : request.gatherConstructed? catalog read parent.context = some ⟨base, collection⟩) :
    ∃ following : base.Realization,
      Nonempty (Shared.Model (reader := OwnerReader.reconciled following following.reference.model)
        collection.shared following following.reference.model) := by
  obtain ⟨packet, constructed, gathered⟩ :=
    request.gatherConstructed?_gathered catalog read parent.context base collection accepted
  have nextModels := packet.models models read valid parent request.providerKeys
  obtain ⟨candidate, installed, provider, modeled, selected, following, history, coherent⟩ :=
    request.gatherReconciledFrom?_history nextModels base collection gathered
  exact ⟨following, coherent⟩

end Hex.RealClosure.Tower
