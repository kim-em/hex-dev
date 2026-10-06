/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.ReconciledBase
public import HexRealClosureMathlib.ReconciledRealization

public section

namespace Hex.RealClosure.BaseContext

/-- Semantic premises for each actual prefix retained by the immutable native
catalog. Insertion retains the supplied provider model and all previous models. -/
def Catalog.Models {registry : Registry} (catalog : Catalog registry) : Prop :=
  ∀ candidate ∈ catalog.prefixes, ∃ model : RealPrefix.Model registry, model.context = candidate

/-- Retrieve the supplied model of an actual installed native prefix. -/
theorem Catalog.Models.model {registry : Registry} {catalog : Catalog registry}
    (models : Catalog.Models catalog) (candidate : RealPrefix registry)
    (installed : candidate ∈ catalog.prefixes) :
    ∃ provider : RealPrefix.Model registry, provider.context = candidate := models candidate installed

/-- The selected realization retains the exact installed provider model and
its automatically chosen depth, including the equality of interpretation histories. -/
theorem Catalog.Models.history {registry : Registry} {catalog : Catalog registry}
    (models : Catalog.Models catalog) (candidate : RealPrefix registry)
    (installed : candidate ∈ catalog.prefixes) (depth : Nat)
    (base : PackedContext registry) (selected : base = candidate.finish.extend depth) :
    ∃ provider : RealPrefix.Model registry, provider.context = candidate ∧
      ∃ following : base.Realization, HEq following (provider.staged depth) := by
  obtain ⟨provider, modeled⟩ := models.model candidate installed
  rw [← modeled] at selected
  subst base
  exact ⟨provider, modeled, provider.staged depth, HEq.rfl⟩

/-- The empty native catalog has its actual rational prefix model. -/
theorem Catalog.Models.empty (registry : Registry) : Catalog.Models (Catalog.empty registry) := by
  intro candidate member
  rw [Catalog.prefixes_empty] at member
  have same := List.mem_singleton.mp member
  refine ⟨RealPrefix.Model.rational registry, ?_⟩
  rw [same]
  exact RealPrefix.Model.rational_context registry

/-- Installing a modeled prefix preserves models of every installed native
prefix, without rebinding existing entries or requesting new agreements. -/
theorem Catalog.Models.insert {registry : Registry} {catalog next : Catalog registry}
    (models : Catalog.Models catalog) (provider : RealPrefix.Model registry)
    (inserted : catalog.insert provider.context = some next) : Catalog.Models next := by
  intro candidate member
  rcases (Catalog.mem_prefixes_of_insert catalog next provider.context candidate inserted).mp member
    with same | earlier
  · exact ⟨provider, same.symm⟩
  · exact models candidate earlier

/-- Recover the interpretation of an actual selected prefix and depth. -/
theorem Catalog.Models.realization {registry : Registry} {catalog : Catalog registry}
    (models : Catalog.Models catalog) (candidate : RealPrefix registry)
    (installed : candidate ∈ catalog.prefixes) (depth : Nat)
    (base : PackedContext registry) (selected : base = candidate.finish.extend depth) :
    Nonempty base.Realization := by
  obtain ⟨provider, modeled⟩ := models candidate installed
  rw [← modeled] at selected
  subst base
  exact ⟨provider.staged depth⟩

end Hex.RealClosure.BaseContext

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry} {catalog : BaseContext.Catalog registry}

/-- An installed jointly compatible prefix makes the actual automatic gather
succeed. Interpretation comes from whichever prefix the native search chooses. -/
theorem Shared.gatherReconciledFrom?_success (models : catalog.Models)
    (owners : List (Context registry)) (candidate : BaseContext.RealPrefix registry)
    (installed : candidate ∈ catalog.prefixes)
    (keys : ∀ owner ∈ owners, owner.origin.base.signature.constants.Nodup ∧
      owner.origin.base.signature.constants ⊆ candidate.keys) :
    (Shared.gatherReconciledFrom? catalog owners).isSome = true := by
  have distinct : candidate.keys.Nodup := by
    obtain ⟨provider, modeled⟩ := models.model candidate installed
    rw [← modeled]
    simpa only [BaseContext.RealPrefix.finish_signature] using provider.realization.keys_nodup
  have available := SharedBase.chooseReconciled?_success catalog (owners.map (·.origin.base))
    candidate installed distinct (by
      intro source member
      obtain ⟨owner, owned, same⟩ := List.mem_map.mp member
      subst source
      exact keys owner owned)
  obtain ⟨chosen, selected⟩ := Option.isSome_iff_exists.mp available
  obtain ⟨actual, installed, target⟩ :=
    SharedBase.chooseReconciled?_target catalog _ chosen selected
  obtain ⟨following⟩ := models.realization actual installed _ chosen.target target
  obtain ⟨shared, gathered, _⟩ := Shared.gatherReconciled?_models following following.reference.model
    owners (by
      intro owner member
      exact chosen.included owner.origin.base (List.mem_map.mpr ⟨owner, member, rfl⟩))
  rw [Shared.gatherReconciledFrom?_of_success catalog owners chosen selected shared gathered]
  rfl

/-- A complete live request fits the catalog whenever one installed prefix
contains every distinct original provider path, in any order. -/
theorem Live.Request.gatherReconciledFrom?_success (models : catalog.Models)
    (request : Live.Request registry) (candidate : BaseContext.RealPrefix registry)
    (installed : candidate ∈ catalog.prefixes)
    (keys : ∀ owner ∈ request.owners, owner.origin.base.signature.constants.Nodup ∧
      owner.origin.base.signature.constants ⊆ candidate.keys) :
    (request.gatherReconciledFrom? catalog).isSome = true := by
  have distinct : candidate.keys.Nodup := by
    obtain ⟨provider, modeled⟩ := models.model candidate installed
    rw [← modeled]
    simpa only [BaseContext.RealPrefix.finish_signature] using provider.realization.keys_nodup
  have available := SharedBase.chooseReconciled?_success catalog (request.owners.map (·.origin.base))
    candidate installed distinct (by
      intro source member
      obtain ⟨owner, owned, same⟩ := List.mem_map.mp member
      subst source
      exact keys owner owned)
  obtain ⟨chosen, selected⟩ := Option.isSome_iff_exists.mp available
  obtain ⟨actual, installed, target⟩ :=
    SharedBase.chooseReconciled?_target catalog _ chosen selected
  obtain ⟨following⟩ := models.realization actual installed _ chosen.target target
  obtain ⟨collection, gathered, _⟩ := Live.Request.gatherReconciled?_models following
    following.reference.model request (by
      intro owner member
      exact chosen.included owner.origin.base (List.mem_map.mpr ⟨owner, member, rfl⟩))
  rw [Live.Request.gatherReconciledFrom?_of_success catalog request chosen selected collection gathered]
  rfl

/-- An accepted automatic result retains the actual catalog model, selected
prefix and depth together with its canonical owner interpretation. -/
theorem Shared.gatherReconciledFrom?_history (models : catalog.Models)
    (owners : List (Context registry)) (base : BaseContext.PackedContext registry)
    (shared : Shared base owners)
    (accepted : Shared.gatherReconciledFrom? catalog owners = some ⟨base, shared⟩) :
    ∃ candidate ∈ catalog.prefixes, ∃ provider : BaseContext.RealPrefix.Model registry,
      provider.context = candidate ∧
        base = candidate.finish.extend (SharedBase.depth (owners.map (·.origin.base))) ∧
          ∃ following : base.Realization,
            HEq following (provider.staged (SharedBase.depth (owners.map (·.origin.base)))) ∧
              Nonempty (Shared.Model
                (reader := OwnerReader.reconciled following following.reference.model)
                shared following following.reference.model) := by
  obtain ⟨candidate, installed, selected⟩ :=
    Shared.gatherReconciledFrom?_base catalog owners base shared accepted
  obtain ⟨provider, modeled, following, exactHistory⟩ :=
    models.history candidate installed _ base selected
  exact ⟨candidate, installed, provider, modeled, selected, following, exactHistory,
    ⟨Shared.Model.ofReconciledGather following following.reference.model owners shared
      (Shared.gatherReconciledFrom?_gathered catalog owners base shared accepted)⟩⟩

/-- An accepted automatic result retains the actual catalog model, selected
prefix and depth together with its canonical owner interpretation. -/
theorem Live.Request.gatherReconciledFrom?_history (models : catalog.Models)
    (request : Live.Request registry) (base : BaseContext.PackedContext registry)
    (collection : Live.Collection base request)
    (accepted : request.gatherReconciledFrom? catalog = some ⟨base, collection⟩) :
    ∃ candidate ∈ catalog.prefixes, ∃ provider : BaseContext.RealPrefix.Model registry,
      provider.context = candidate ∧
        base = candidate.finish.extend (SharedBase.depth (request.owners.map (·.origin.base))) ∧
          ∃ following : base.Realization,
            HEq following (provider.staged (SharedBase.depth (request.owners.map (·.origin.base)))) ∧
              Nonempty (Shared.Model
                (reader := OwnerReader.reconciled following following.reference.model)
                collection.shared following following.reference.model) := by
  obtain ⟨candidate, installed, selected⟩ :=
    Live.Request.gatherReconciledFrom?_base catalog request base collection accepted
  obtain ⟨provider, modeled, following, exactHistory⟩ :=
    models.history candidate installed _ base selected
  exact ⟨candidate, installed, provider, modeled, selected, following, exactHistory,
    ⟨collection.reconciledModel following following.reference.model
      (Live.Request.gatherReconciledFrom?_gathered catalog request base collection accepted)⟩⟩

/-- An accepted automatic gather has one canonical interpretation derived from
its actual catalog prefix. No target or source realization is supplied. -/
theorem Shared.gatherReconciledFrom?_models (models : catalog.Models)
    (owners : List (Context registry)) (base : BaseContext.PackedContext registry)
    (shared : Shared base owners)
    (accepted : Shared.gatherReconciledFrom? catalog owners = some ⟨base, shared⟩) :
    ∃ following : base.Realization,
      Nonempty (Shared.Model (reader := OwnerReader.reconciled following following.reference.model)
        shared following following.reference.model) := by
  obtain ⟨candidate, installed, selected⟩ :=
    Shared.gatherReconciledFrom?_base catalog owners base shared accepted
  obtain ⟨following⟩ := models.realization candidate installed _ base selected
  exact ⟨following, ⟨Shared.Model.ofReconciledGather following following.reference.model owners shared
    (Shared.gatherReconciledFrom?_gathered catalog owners base shared accepted)⟩⟩

/-- The actual installed catalog model supplies the common target history for
an accepted complete live collection, including its canonical owner cache. -/
theorem Live.Request.gatherReconciledFrom?_models (models : catalog.Models)
    (request : Live.Request registry) (base : BaseContext.PackedContext registry)
    (collection : Live.Collection base request)
    (accepted : request.gatherReconciledFrom? catalog = some ⟨base, collection⟩) :
    ∃ following : base.Realization,
      Nonempty (Shared.Model (reader := OwnerReader.reconciled following following.reference.model)
        collection.shared following following.reference.model) := by
  obtain ⟨candidate, installed, selected⟩ :=
    Live.Request.gatherReconciledFrom?_base catalog request base collection accepted
  obtain ⟨following⟩ := models.realization candidate installed _ base selected
  exact ⟨following, ⟨collection.reconciledModel following following.reference.model
    (Live.Request.gatherReconciledFrom?_gathered catalog request base collection accepted)⟩⟩

/-- All original and refreshed finite live inventories share one ordinary
reader from the actual selected catalog history. -/
theorem Live.Request.gatherReconciledFrom?_realize (models : catalog.Models)
    (request : Live.Request registry) (base : BaseContext.PackedContext registry)
    (collection : Live.Collection base request)
    (accepted : request.gatherReconciledFrom? catalog = some ⟨base, collection⟩) :
    ∃ candidate ∈ catalog.prefixes, ∃ provider : BaseContext.RealPrefix.Model registry,
      provider.context = candidate ∧
        base = candidate.finish.extend (SharedBase.depth (request.owners.map (·.origin.base))) ∧
          ∃ following : base.Realization,
            HEq following (provider.staged (SharedBase.depth (request.owners.map (·.origin.base)))) ∧
              ∃ read : collection.shared.input.context.Value → ℝ,
                ∃ domain : collection.shared.input.context.Value → Prop,
                  collection.shared.Realized following request.inventory collection.inventory read domain := by
  obtain ⟨candidate, installed, provider, modeled, selected, following, exactHistory, _⟩ :=
    Live.Request.gatherReconciledFrom?_history models request base collection accepted
  obtain ⟨read, domain, data⟩ := collection.realizeReconciled following
    (Live.Request.gatherReconciledFrom?_gathered catalog request base collection accepted)
    collection.inventory
  exact ⟨candidate, installed, provider, modeled, selected, following, exactHistory, read, domain, data⟩

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.BaseContext.Catalog.Models.empty' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Catalog.Models.empty

/-- info: 'Hex.RealClosure.BaseContext.Catalog.Models.insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Catalog.Models.insert

/-- info: 'Hex.RealClosure.BaseContext.Catalog.Models.realization' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Catalog.Models.realization

/-- info: 'Hex.RealClosure.Tower.Shared.gatherReconciledFrom?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.gatherReconciledFrom?_success

/-- info: 'Hex.RealClosure.Tower.Shared.gatherReconciledFrom?_models' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.gatherReconciledFrom?_models

/-- info: 'Hex.RealClosure.Tower.Live.Request.gatherReconciledFrom?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Request.gatherReconciledFrom?_success

/-- info: 'Hex.RealClosure.Tower.Live.Request.gatherReconciledFrom?_models' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Request.gatherReconciledFrom?_models

/-- info: 'Hex.RealClosure.Tower.Live.Request.gatherReconciledFrom?_realize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Request.gatherReconciledFrom?_realize

/-- info: 'Hex.RealClosure.BaseContext.Catalog.Models.model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Catalog.Models.model

/-- info: 'Hex.RealClosure.BaseContext.Catalog.Models.history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Catalog.Models.history

/-- info: 'Hex.RealClosure.Tower.Shared.gatherReconciledFrom?_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.gatherReconciledFrom?_history

/-- info: 'Hex.RealClosure.Tower.Live.Request.gatherReconciledFrom?_history' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Request.gatherReconciledFrom?_history
