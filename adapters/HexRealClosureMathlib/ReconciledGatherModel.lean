/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.ReconciledGather
public import HexRealClosureMathlib.CacheGather
public import HexRealClosureMathlib.ReconciledContext
import all HexRealClosure.ReconciledGather
import all HexRealClosureMathlib.CacheGather

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry} {base : BaseContext.PackedContext registry}
variable {R : Type u} [Field R] [LinearOrder R] [DecidableEq R]
variable [IsStrictOrderedRing R] [IsRealClosed R]

/-- The checked provider reconciliation supplies the cache entry's canonical
source interpretation and its coefficient agreement in the retained target. -/
noncomputable def InclusionCache.EntryModel.ofReconciledBase
    (source : BaseContext.PackedContext registry) (following : base.Realization)
    (reference : Tower.Model (Context.ofBase base) R)
    (inclusion : BaseReconciliation source base)
    (produced : BaseReconciliation.make? source base = some inclusion) :
    InclusionCache.EntryModel (reader := OwnerReader.reconciled following reference)
      following reference reference
      ⟨Conversion.reconcileBase inclusion, (Conversion.reconcileBase_spec inclusion).1⟩ where
  original := (BaseReconciliation.Model.deriveCanonical following inclusion reference).source
  produced := Context.reconciledModel?_baseMap source following reference inclusion produced
  value := by
    intro a
    have preserved := (BaseReconciliation.Model.deriveCanonical following inclusion reference).value a
    rw [BaseReconciliation.Model.deriveCanonical_target] at preserved
    exact preserved

/-- Registering a compatible owner derives its interpretation from the target
provider history. Every existing owner and cache entry keeps that same model,
and the returned predecessor map preserves the previous shared target. -/
theorem Shared.Model.registerReconciledOrigin?_models {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    (model : Shared.Model (reader := OwnerReader.reconciled following reference)
      shared following reference)
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (original : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base original)) {source : Context registry}
    (same : suffix.context = source)
    (compatible : (BaseContext.PackedContext.pack original).signature.constants.Nodup ∧
      (BaseContext.PackedContext.pack original).signature.constants ⊆ base.signature.constants ∧
      (BaseContext.PackedContext.pack original).signature.infinitesimals ≤
        base.signature.infinitesimals) :
    ∃ packet : Registration shared source,
      shared.registerReconciledOrigin? (.pack original suffix same) = some packet ∧
        ∃ returned : Shared.Model (reader := OwnerReader.reconciled following reference)
            packet.shared following reference,
          ∀ a, returned.target.value (packet.previous.value a) = model.target.value a := by
  cases same
  let reader := OwnerReader.reconciled following reference
  have success := BaseReconciliation.make?_success (.pack original) base
    compatible.1 following.keys_nodup compatible.2.1 compatible.2.2
  obtain ⟨coefficients, produced⟩ := Option.isSome_iff_exists.mp success
  let previous : Inclusion (Context.base original) (Context.ofBase base) :=
    ⟨Conversion.reconcileBase coefficients, (Conversion.reconcileBase_spec coefficients).1⟩
  have baseProduced : Inclusion.reconcileBase? (.pack original) base = some previous := by
    rw [Inclusion.reconcileBase?_eq, produced]
    rfl
  let current : Inclusion (Context.ofBase base) shared.input.context := ⟨shared.input, rfl⟩
  let initial := previous.comp current
  have currentValue : ∀ a, model.target.value (current.value a) = reference.value a :=
    model.input
  let incoming : InclusionCache.EntryModel (reader := reader)
      following reference model.target initial :=
    (InclusionCache.EntryModel.ofReconciledBase (.pack original) following reference
      coefficients produced).transport current model.target currentValue
  obtain ⟨rebuilt, rebuiltProduced, ⟨interpreted⟩⟩ :=
    shared.cache.rebuild?_models (reader := reader) following reference model.target model.cache
      model.canonical initial incoming suffix
  obtain ⟨packet, resultProduced, inputEq, previousEq, mapsEq, cacheEq⟩ :=
    shared.registerBase?_spec original suffix rfl previous rebuilt rebuiltProduced
  have registered : shared.registerReconciledOrigin? (.pack original suffix rfl) =
      some packet := by
    unfold Shared.registerReconciledOrigin?
    change (Inclusion.reconcileBase? (.pack original) base).bind
      (fun inclusion => shared.registerBase? (.pack original suffix rfl) inclusion) = some packet
    rw [baseProduced]
    exact resultProduced
  let result := packet.shared
  let combined := (current.comp rebuilt.inclusion).native
  have canonical : reader.read combined.context = some interpreted.target :=
    interpreted.produced
  have preserved : ∀ a, interpreted.target.value (combined.value a) = reference.value a := by
    intro a
    change interpreted.target.value ((current.comp rebuilt.inclusion).value a) = reference.value a
    rw [Inclusion.comp_value, interpreted.previous, currentValue]
  let nextModel := Inclusion.Model.ofValues rebuilt.inclusion model.target
    interpreted.target interpreted.previous
  have aligned : nextModel.target = interpreted.target :=
    Inclusion.Model.ofValues_target _ _ _ _
  have family : ∃ ownersModel : Inclusions.Models interpreted.target
      ((shared.maps.extend rebuilt.inclusion).snoc rebuilt.original),
      ∀ index : Fin (owners ++ [suffix.context]).length,
        reader.read ((owners ++ [suffix.context])[index]) =
          some (ownersModel.get index).1 := by
    let previousModels := model.owners.extend nextModel
    have previousCanonical : ∀ index : Fin owners.length,
        reader.read (owners[index]) = some (previousModels.get index).1 := by
      intro index
      change reader.read (owners[index]) =
        some (((model.owners.extend nextModel).get index).1)
      rw [Inclusions.Models.extend_original]
      exact model.canonicalOwners index
    let fixedModels := castModels aligned previousModels
    have fixedCanonical : ∀ index : Fin owners.length,
        reader.read (owners[index]) = some (fixedModels.get index).1 := by
      intro index
      rw [castModels_original]
      exact previousCanonical index
    exact ⟨fixedModels.snoc interpreted.original.original interpreted.original.inclusion
      interpreted.original.inclusion_target,
      canonical_snoc reader fixedModels fixedCanonical interpreted.original.original
        interpreted.original.inclusion interpreted.original.inclusion_target
        interpreted.original.produced⟩
  obtain ⟨ownersModel, canonicalOwners⟩ := family
  let returned := Shared.Model.ofParts (reader := reader) result following reference
    combined inputEq interpreted.target canonical preserved _ mapsEq ownersModel canonicalOwners
    rebuilt.cache cacheEq interpreted.cache
  have retainedValue := Shared.Model.ofParts_value (reader := reader) result following reference
    combined inputEq interpreted.target canonical preserved _ mapsEq ownersModel canonicalOwners
    rebuilt.cache cacheEq interpreted.cache model.target rebuilt.inclusion interpreted.previous
    packet.previous previousEq
  exact ⟨packet, registered, returned, retainedValue⟩

/-- The empty reconciled collection uses the supplied target interpretation
and has no owner or cache agreement obligations. -/
noncomputable def Shared.Model.emptyReconciled (following : base.Realization)
    (reference : Tower.Model (Context.ofBase base) R) :
    Shared.Model (reader := OwnerReader.reconciled following reference)
      (Shared.empty base) following reference := by
  let reader := OwnerReader.reconciled following reference
  let conversion := Conversion.identity (Context.ofBase base)
  let model := Conversion.Model.identity reference
  have same := Shared.empty_input base
  have contextEq : (Shared.empty base).input.context = conversion.context :=
    congrArg Conversion.context same
  have canonical : reader.read conversion.context = some model.target :=
    model_produced_cast reader (Conversion.identity_spec _).1.symm
      reference model.target (Conversion.Model.identity_target reference)
      (Context.reconciledModel?_base following reference)
  have mapsEq : HEq (Shared.empty base).maps
      (Inclusions.nil (target := conversion.context)) :=
    (Shared.empty_maps base).trans (nil_heq contextEq)
  have cacheEq : HEq (Shared.empty base).cache
      (⟨[], []⟩ : InclusionCache conversion.context) :=
    cache_empty_heq contextEq _ (Shared.empty_entries base) (Shared.empty_candidates base)
  exact Shared.Model.ofParts (reader := reader) (Shared.empty base) following reference
    conversion same model.target canonical model.value .nil mapsEq .nil
    (fun index => nomatch index) ⟨[], []⟩ cacheEq
    (InclusionCache.Models.empty (reader := reader) model.target)

/-- Public registration retains the checked map from the previous shared
target and canonical interpretations of all owners and cache entries. -/
theorem Shared.Model.registerReconciled? {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    (model : Shared.Model (reader := OwnerReader.reconciled following reference)
      shared following reference) (source : Context registry)
    (compatible : source.origin.base.signature.constants.Nodup ∧
      source.origin.base.signature.constants ⊆ base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals) :
    ∃ packet : Registration shared source,
      shared.registerReconciled? source = some packet ∧
        ∃ returned : Shared.Model (reader := OwnerReader.reconciled following reference)
            packet.shared following reference,
          ∀ a, returned.target.value (packet.previous.value a) = model.target.value a := by
  unfold Shared.registerReconciled?
  cases originEq : source.origin with
  | pack original suffix same =>
    rw [originEq] at compatible
    exact model.registerReconciledOrigin?_models original suffix same compatible

/-- Adding a compatible owner preserves canonical cache and owner models. -/
theorem Shared.Model.addReconciled? {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    (model : Shared.Model (reader := OwnerReader.reconciled following reference)
      shared following reference) (source : Context registry)
    (compatible : source.origin.base.signature.constants.Nodup ∧
      source.origin.base.signature.constants ⊆ base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals) :
    ∃ result, shared.addReconciled? source = some result ∧
      Nonempty (Shared.Model (reader := OwnerReader.reconciled following reference)
        result following reference) := by
  obtain ⟨packet, produced, returned, _⟩ := model.registerReconciled? source compatible
  refine ⟨packet.shared, ?_, ⟨returned⟩⟩
  simp only [Shared.addReconciled?, produced, Option.map_some]

/-- Collecting compatible contexts accepts any provider-key order and retains
one canonical interpretation of every owner and rebuilt predecessor. -/
theorem Shared.Model.collectReconciled? {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    (model : Shared.Model (reader := OwnerReader.reconciled following reference)
      shared following reference) (later : List (Context registry))
    (compatible : ∀ source ∈ later,
      source.origin.base.signature.constants.Nodup ∧
      source.origin.base.signature.constants ⊆ base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals) :
    ∃ result, shared.collectReconciled? later = some result ∧
      Nonempty (Shared.Model (reader := OwnerReader.reconciled following reference)
        result following reference) := by
  induction later generalizing owners with
  | nil =>
    refine ⟨_, rfl, ⟨model.castOwners (List.append_nil owners).symm
      shared following reference⟩⟩
  | cons source rest ih =>
    obtain ⟨added, addedProduced, ⟨addedModel⟩⟩ :=
      model.addReconciled? source (compatible source (List.mem_cons_self ..))
    obtain ⟨result, resultProduced, ⟨resultModel⟩⟩ :=
      ih addedModel (fun source present => compatible source (List.mem_cons_of_mem _ present))
    refine ⟨_, ?_, ⟨resultModel.castOwners (List.append_assoc owners [source] rest)
      result following reference⟩⟩
    simp only [Shared.collectReconciled?, addedProduced, bind, Option.bind,
      resultProduced, pure]

/-- One validated target history suffices to gather all compatible native
contexts, reconstruct their owners and prove coherence of the actual cache. -/
theorem Shared.gatherReconciled?_models (following : base.Realization)
    (reference : Tower.Model (Context.ofBase base) R) (owners : List (Context registry))
    (compatible : ∀ source ∈ owners,
      source.origin.base.signature.constants.Nodup ∧
      source.origin.base.signature.constants ⊆ base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals) :
    ∃ result, Shared.gatherReconciled? base owners = some result ∧
      Nonempty (Shared.Model (reader := OwnerReader.reconciled following reference)
        result following reference) := by
  unfold Shared.gatherReconciled?
  exact (Shared.Model.emptyReconciled following reference).collectReconciled? owners compatible

/-- Interpret an already accepted native gather. Its actual provider checks
derive every source compatibility premise used by the model construction. -/
noncomputable def Shared.Model.ofReconciledGather (following : base.Realization)
    (reference : Tower.Model (Context.ofBase base) R) (owners : List (Context registry))
    (shared : Shared base owners)
    (produced : Shared.gatherReconciled? base owners = some shared) :
    Shared.Model (reader := OwnerReader.reconciled following reference)
      shared following reference := Classical.choice (by
  obtain ⟨result, resultProduced, models⟩ :=
    Shared.gatherReconciled?_models following reference owners
      (Shared.gatherReconciled?_compatible base following.keys_nodup owners shared produced)
  have same := Option.some.inj (resultProduced.symm.trans produced)
  cases same
  exact models)

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.InclusionCache.EntryModel.ofReconciledBase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.InclusionCache.EntryModel.ofReconciledBase

/-- info: 'Hex.RealClosure.Tower.Shared.Model.registerReconciledOrigin?_models' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.Model.registerReconciledOrigin?_models

/-- info: 'Hex.RealClosure.Tower.Shared.Model.collectReconciled?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.Model.collectReconciled?

/-- info: 'Hex.RealClosure.Tower.Shared.gatherReconciled?_models' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.gatherReconciled?_models

/-- info: 'Hex.RealClosure.Tower.Shared.Model.ofReconciledGather' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.Model.ofReconciledGather
