/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.CacheRebuild
import all HexRealClosure.LiveContext

public section

namespace Hex.RealClosure.Tower

open scoped Hex.OrderedFn.Infinitesimal

variable {registry : BaseContext.Registry} {base : BaseContext.PackedContext registry}
variable {R : Type u} [Field R] [LinearOrder R] [DecidableEq R]
variable [IsStrictOrderedRing R] [IsRealClosed R]

private theorem model_target_cast {source : Context registry}
    {S : Type v} [Field S] [LinearOrder S]
    {left right : Tower.Model source S} (same : left = right)
    {conversion : Conversion source} (model : Conversion.Model conversion left) :
    HEq (same ▸ model).target model.target := by
  cases same
  rfl

private theorem conversion_target_cast {source : Context registry}
    {S : Type v} [Field S] [LinearOrder S]
    {left right : Conversion source} (same : left = right)
    {original : Tower.Model source S} (model : Conversion.Model left original) :
    HEq (same ▸ model).target model.target := by
  cases same
  rfl

private theorem restrict_model {source target : Context registry}
    (suffix : Suffix source) (same : suffix.context = target)
    (reference : Tower.Model source R) (old : Tower.Model target R)
    (canonical : (same ▸ reference.extend suffix) = old) :
    suffix.restrict reference (same.symm ▸ old) = reference := by
  cases same
  cases canonical
  apply Tower.Model.value_ext
  intro a
  rw [Suffix.restrict_value, Tower.Model.extend_embed]

private noncomputable def cache_cast {source destination : Context registry}
    (same : source = destination) (following : base.Realization)
    {S : Type v} [Field S] [LinearOrder S] [DecidableEq S]
    [IsStrictOrderedRing S] [IsRealClosed S]
    (reference : Tower.Model (Context.ofBase base) S)
    (sourceModel : Tower.Model source S) (targetModel : Tower.Model destination S)
    (aligned : HEq targetModel sourceModel) (cache : InclusionCache source)
    (models : InclusionCache.Models following reference sourceModel cache) :
    InclusionCache.Models following reference targetModel (same ▸ cache) := by
  cases same
  cases eq_of_heq aligned
  exact models

/-- One factory-derived interpretation of the actual shared target, original
owners, and predecessor cache. No independent coefficient agreement is required. -/
structure Shared.Model {contexts : List (Context registry)} (shared : Shared base contexts)
    (following : base.Realization) (reference : Tower.Model (Context.ofBase base) R) where
  target : Tower.Model shared.input.context R
  canonical : shared.input.context.model? following reference = some target
  input : ∀ a, target.value (shared.input.value a) = reference.value a
  owners : Inclusions.Models target shared.maps
  canonicalOwners : ∀ index : Fin contexts.length,
    (contexts[index]).model? following reference = some (owners.get index).1
  cache : InclusionCache.Models following reference target shared.cache

private theorem Shared.Model.suffix
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign) {owners : List (Context registry)}
    {shared : Shared (.pack base) owners}
    {following : (BaseContext.PackedContext.pack base).Realization}
    {reference : Tower.Model (Context.base base) R}
    (model : Shared.Model shared following reference)
    (suffix : Suffix (Context.base base)) (same : suffix.context = shared.input.context)
    (origin : shared.input.context.origin = Origin.pack base suffix same) :
    (same ▸ reference.extend suffix) = model.target := by
  have baseCanonical : (Context.base base).model? following reference = some reference :=
    Context.model?_base following reference
  have canonical := (Context.model?_origin shared.input.context following reference).trans
    ((congrArg (fun original : Origin shared.input.context =>
      original.model? following reference) origin).trans
      (Origin.model?_pack base suffix same following reference))
  have extended := congrArg (fun original : Option (Tower.Model (Context.base base) R) =>
    original.map (fun interpreted => same ▸ interpreted.extend suffix)) baseCanonical
  exact Option.some.inj ((canonical.trans extended).symm.trans model.canonical)

private theorem model_produced_cast (following : base.Realization)
    (reference : Tower.Model (Context.ofBase base) R)
    {left right : Context registry} (same : left = right)
    (original : Tower.Model left R) (target : Tower.Model right R)
    (aligned : HEq target original)
    (produced : left.model? following reference = some original) :
    right.model? following reference = some target := by
  cases same
  cases eq_of_heq aligned
  exact produced

private noncomputable def Shared.Model.ofParts {owners : List (Context registry)}
    (shared : Shared base owners) (following : base.Realization)
    (reference : Tower.Model (Context.ofBase base) R)
    (conversion : Conversion (Context.ofBase base)) (same : shared.input = conversion)
    (target : Tower.Model conversion.context R)
    (canonical : conversion.context.model? following reference = some target)
    (preserved : ∀ a, target.value (conversion.value a) = reference.value a)
    (maps : Inclusions conversion.context owners) (mapsEq : HEq shared.maps maps)
    (ownersModel : Inclusions.Models target maps)
    (canonicalOwners : ∀ index : Fin owners.length,
      (owners[index]).model? following reference = some (ownersModel.get index).1)
    (cache : InclusionCache conversion.context) (cacheEq : HEq shared.cache cache)
    (cacheModel : InclusionCache.Models following reference target cache) :
    Shared.Model shared following reference := by
  cases same
  cases eq_of_heq mapsEq
  cases eq_of_heq cacheEq
  exact ⟨target, canonical, preserved, ownersModel, canonicalOwners, cacheModel⟩

private theorem Shared.Model.ofParts_value {owners : List (Context registry)}
    (shared : Shared base owners) (following : base.Realization)
    (reference : Tower.Model (Context.ofBase base) R)
    (conversion : Conversion (Context.ofBase base)) (same : shared.input = conversion)
    (target : Tower.Model conversion.context R)
    (canonical : conversion.context.model? following reference = some target)
    (preserved : ∀ a, target.value (conversion.value a) = reference.value a)
    (maps : Inclusions conversion.context owners) (mapsEq : HEq shared.maps maps)
    (ownersModel : Inclusions.Models target maps)
    (canonicalOwners : ∀ index : Fin owners.length,
      (owners[index]).model? following reference = some (ownersModel.get index).1)
    (cache : InclusionCache conversion.context) (cacheEq : HEq shared.cache cache)
    (cacheModel : InclusionCache.Models following reference target cache)
    {source : Context registry} (old : Tower.Model source R)
    (previous : Inclusion source conversion.context)
    (previousValue : ∀ a, target.value (previous.value a) = old.value a)
    (retained : Inclusion source shared.input.context) (retainedEq : HEq retained previous) :
      ∀ a, (Shared.Model.ofParts shared following reference conversion same target canonical
        preserved maps mapsEq ownersModel canonicalOwners cache cacheEq cacheModel).target.value
          (retained.value a) = old.value a := by
  cases same
  cases eq_of_heq mapsEq
  cases eq_of_heq cacheEq
  cases eq_of_heq retainedEq
  exact previousValue

private theorem nil_heq {left right : Context registry} (same : left = right) :
    HEq (Inclusions.nil (target := left)) (Inclusions.nil (target := right)) := by
  cases same
  rfl

private theorem cache_empty_heq {left right : Context registry} (same : left = right)
    (cache : InclusionCache left) (empty : cache.entries = [])
    (candidates : cache.candidates = []) :
    HEq cache (⟨[], []⟩ : InclusionCache right) := by
  cases same
  cases cache
  cases empty
  cases candidates
  rfl

/-- The actual empty collection has the supplied base interpretation and a
coherent empty owner family and predecessor cache. -/
noncomputable def Shared.Model.empty (following : base.Realization)
    (reference : Tower.Model (Context.ofBase base) R) :
    Shared.Model (Shared.empty base) following reference := by
  let conversion := Conversion.identity (Context.ofBase base)
  let model := Conversion.Model.identity reference
  have same := Shared.empty_input base
  have contextEq : (Shared.empty base).input.context = conversion.context :=
    congrArg Conversion.context same
  have canonical : conversion.context.model? following reference = some model.target :=
    model_produced_cast following reference (Conversion.identity_spec _).1.symm
      reference model.target (Conversion.Model.identity_target reference)
      (Context.model?_base following reference)
  have mapsEq : HEq (Shared.empty base).maps
      (Inclusions.nil (target := conversion.context)) :=
    (Shared.empty_maps base).trans (nil_heq contextEq)
  have cacheEq : HEq (Shared.empty base).cache
      (⟨[], []⟩ : InclusionCache conversion.context) :=
    cache_empty_heq contextEq _ (Shared.empty_entries base) (Shared.empty_candidates base)
  exact Shared.Model.ofParts (Shared.empty base) following reference conversion same
    model.target canonical model.value .nil mapsEq .nil (fun index => nomatch index) ⟨[], []⟩ cacheEq
    (InclusionCache.Models.empty model.target)

private noncomputable def castEntry {left right destination : Context registry}
    (same : left = right) {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    {target : Tower.Model destination R} {inclusion : Inclusion left destination}
    (model : InclusionCache.EntryModel following reference target inclusion) :
    InclusionCache.EntryModel following reference target
      (_root_.cast (congrArg (fun context => Inclusion context destination) same) inclusion) := by
  cases same
  exact model

private noncomputable def castModels {destination : Context registry}
    {contexts : List (Context registry)} {maps : Inclusions destination contexts}
    {left right : Tower.Model destination R} (same : left = right)
    (models : Inclusions.Models left maps) : Inclusions.Models right maps := same ▸ models

private theorem castModels_original {destination : Context registry}
    {contexts : List (Context registry)} {maps : Inclusions destination contexts}
    {left right : Tower.Model destination R} (same : left = right)
    (models : Inclusions.Models left maps) (index : Fin contexts.length) :
    ((castModels same models).get index).1 = (models.get index).1 := by
  cases same
  rfl

private theorem canonical_snoc {destination source : Context registry}
    {following : base.Realization} {reference : Tower.Model (Context.ofBase base) R}
    {contexts : List (Context registry)} {maps : Inclusions destination contexts}
    {target : Tower.Model destination R} (models : Inclusions.Models target maps)
    (canonical : ∀ index : Fin contexts.length,
      (contexts[index]).model? following reference = some (models.get index).1)
    {next : Inclusion source destination} (original : Tower.Model source R)
    (checked : Inclusion.Model next original) (aligned : checked.target = target)
    (produced : source.model? following reference = some original) :
    ∀ index : Fin (contexts ++ [source]).length,
      ((contexts ++ [source])[index]).model? following reference =
        some ((models.snoc original checked aligned).get index).1 := by
  induction models with
  | nil =>
    intro index
    rcases index with ⟨index, valid⟩
    have zero : index = 0 := by simpa only [List.nil_append, List.length_singleton,
      Nat.lt_one_iff] using valid
    subst index
    exact produced
  | @cons owner rest head tail previous model same later ih =>
    intro index
    rcases index with ⟨index, valid⟩
    cases index with
    | zero => exact canonical ⟨0, by simp⟩
    | succ index =>
      exact ih (fun i => canonical ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩)
        ⟨index, Nat.lt_of_succ_lt_succ valid⟩

/-- Registration derives the original base interpretation from the target
provider history, and returns coherent models for all owners and cache entries.
Compatibility checks the original staged base; no cache agreement is supplied. -/
theorem Shared.Model.registerOrigin?_models {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    (model : Shared.Model shared following reference)
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (original : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base original)) {source : Context registry}
    (same : suffix.context = source)
    (compatible : (BaseContext.PackedContext.pack original).signature.constants <+:
      base.signature.constants ∧
      (BaseContext.PackedContext.pack original).signature.infinitesimals ≤
        base.signature.infinitesimals) :
    ∃ packet : Registration shared source,
      shared.registerOrigin? (.pack original suffix same) = some packet ∧
        ∃ returned : Shared.Model packet.shared following reference,
          ∀ a, returned.target.value (packet.previous.value a) = model.target.value a := by
  have success := (BaseInclusion.make?_isSome (.pack original) base).mpr compatible
  obtain ⟨coefficients, produced⟩ := Option.isSome_iff_exists.mp success
  let previous : Inclusion (Context.base original) (Context.ofBase base) :=
    ⟨Conversion.base coefficients, (Conversion.base_spec coefficients).1⟩
  have baseProduced : Inclusion.base? (.pack original) base = some previous := by
    rw [Inclusion.base?_eq, produced]
    rfl
  let current : Inclusion (Context.ofBase base) shared.input.context := ⟨shared.input, rfl⟩
  let initial := previous.comp current
  have currentValue : ∀ a, model.target.value (current.value a) = reference.value a :=
    model.input
  let incoming : InclusionCache.EntryModel following reference model.target initial :=
    (InclusionCache.EntryModel.ofBase (.pack original) following reference coefficients produced).transport current model.target currentValue
  obtain ⟨rebuilt, rebuiltProduced, ⟨interpreted⟩⟩ :=
    shared.cache.rebuild?_models following reference model.target model.cache
      model.canonical initial incoming suffix
  obtain ⟨packet, resultProduced, inputEq, previousEq, mapsEq, cacheEq⟩ :=
    shared.registerOrigin?_spec original suffix same previous baseProduced rebuilt rebuiltProduced
  let result := packet.shared
  let combined := (current.comp rebuilt.inclusion).native
  have canonical : combined.context.model? following reference = some interpreted.target :=
    interpreted.produced
  have preserved : ∀ a, interpreted.target.value (combined.value a) = reference.value a := by
    intro a
    change interpreted.target.value ((current.comp rebuilt.inclusion).value a) = reference.value a
    rw [Inclusion.comp_value, interpreted.previous, currentValue]
  let nextModel := Inclusion.Model.ofValues rebuilt.inclusion model.target
    interpreted.target interpreted.previous
  have aligned : nextModel.target = interpreted.target :=
    Inclusion.Model.ofValues_target _ _ _ _
  let originalModel := castEntry same interpreted.original
  have family : ∃ ownersModel : Inclusions.Models interpreted.target
      ((shared.maps.extend rebuilt.inclusion).snoc
        (_root_.cast (congrArg (fun context => Inclusion context rebuilt.target) same)
          rebuilt.original)),
      ∀ index : Fin (owners ++ [source]).length,
        ((owners ++ [source])[index]).model? following reference =
          some (ownersModel.get index).1 := by
    let previousModels := model.owners.extend nextModel
    have previousCanonical : ∀ index : Fin owners.length,
        (owners[index]).model? following reference = some (previousModels.get index).1 := by
      intro index
      change (owners[index]).model? following reference =
        some (((model.owners.extend nextModel).get index).1)
      rw [Inclusions.Models.extend_original]
      exact model.canonicalOwners index
    let fixedModels := castModels aligned previousModels
    have fixedCanonical : ∀ index : Fin owners.length,
        (owners[index]).model? following reference = some (fixedModels.get index).1 := by
      intro index
      rw [castModels_original]
      exact previousCanonical index
    exact ⟨fixedModels.snoc originalModel.original originalModel.inclusion
      originalModel.inclusion_target,
      canonical_snoc fixedModels fixedCanonical originalModel.original
        originalModel.inclusion originalModel.inclusion_target originalModel.produced⟩
  obtain ⟨ownersModel, canonicalOwners⟩ := family
  let returned := Shared.Model.ofParts result following reference
    combined inputEq interpreted.target canonical preserved _ mapsEq ownersModel canonicalOwners
    rebuilt.cache cacheEq interpreted.cache
  have retainedValue := Shared.Model.ofParts_value result following reference
    combined inputEq interpreted.target canonical preserved _ mapsEq ownersModel canonicalOwners
    rebuilt.cache cacheEq interpreted.cache model.target rebuilt.inclusion interpreted.previous
    packet.previous previousEq
  exact ⟨packet, resultProduced, returned, retainedValue⟩

/-- The existing registration surface retains the packet's actual target map. -/
theorem Shared.Model.addOrigin?_transport {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    (model : Shared.Model shared following reference)
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (original : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base original)) {source : Context registry}
    (same : suffix.context = source)
    (compatible : (BaseContext.PackedContext.pack original).signature.constants <+:
      base.signature.constants ∧
      (BaseContext.PackedContext.pack original).signature.infinitesimals ≤
        base.signature.infinitesimals) :
    ∃ result, shared.addOrigin? (.pack original suffix same) = some result ∧
      ∃ returned : Shared.Model result following reference,
        ∃ previous : Inclusion shared.input.context result.input.context,
          ∀ a, returned.target.value (previous.value a) = model.target.value a := by
  obtain ⟨packet, produced, returned, preserved⟩ :=
    model.registerOrigin?_models original suffix same compatible
  have forgotten := congrArg (Option.map Registration.shared) produced
  rw [Shared.registerOrigin?_shared] at forgotten
  exact ⟨packet.shared, forgotten, returned, packet.previous, preserved⟩

/-- Registration preserves coherence of every original owner and cache entry. -/
theorem Shared.Model.addOrigin? {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    (model : Shared.Model shared following reference)
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (original : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base original)) {source : Context registry}
    (same : suffix.context = source)
    (compatible : (BaseContext.PackedContext.pack original).signature.constants <+:
      base.signature.constants ∧
      (BaseContext.PackedContext.pack original).signature.infinitesimals ≤
        base.signature.infinitesimals) :
    ∃ result, shared.addOrigin? (.pack original suffix same) = some result ∧
      Nonempty (Shared.Model result following reference) := by
  obtain ⟨result, produced, returned, _, _⟩ :=
    model.addOrigin?_transport original suffix same compatible
  exact ⟨result, produced, ⟨returned⟩⟩

/-- Public registration needs only compatibility of the original staged base
with the declared target base. All semantic agreements come from the factory. -/
theorem Shared.Model.add? {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    (model : Shared.Model shared following reference) (source : Context registry)
    (compatible : source.origin.base.signature.constants <+: base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals) :
    ∃ result, shared.add? source = some result ∧
      Nonempty (Shared.Model result following reference) := by
  rw [Shared.add?_eq]
  cases originEq : source.origin with
  | pack original suffix same =>
    rw [originEq] at compatible
    exact model.addOrigin? original suffix same compatible

/-- Registration retains an explicit checked inclusion for every value computed
in the previous shared target, interpreted by the returned canonical model. -/
theorem Shared.Model.add?_transport {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    (model : Shared.Model shared following reference) (source : Context registry)
    (compatible : source.origin.base.signature.constants <+: base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals) :
    ∃ result, shared.add? source = some result ∧
      ∃ returned : Shared.Model result following reference,
        ∃ previous : Inclusion shared.input.context result.input.context,
          ∀ a, returned.target.value (previous.value a) = model.target.value a := by
  rw [Shared.add?_eq]
  cases originEq : source.origin with
  | pack original suffix same =>
    rw [originEq] at compatible
    exact model.addOrigin?_transport original suffix same compatible

/-- The executable registration packet and its retained target inclusion are
interpreted by one canonical model, with no caller-supplied value agreement. -/
theorem Shared.Model.register? {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    (model : Shared.Model shared following reference) (source : Context registry)
    (compatible : source.origin.base.signature.constants <+: base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals) :
    ∃ packet : Registration shared source,
      shared.register? source = some packet ∧
        ∃ returned : Shared.Model packet.shared following reference,
          ∀ a, returned.target.value (packet.previous.value a) = model.target.value a := by
  rw [Shared.register?_eq]
  cases originEq : source.origin with
  | pack original suffix same =>
    rw [originEq] at compatible
    exact model.registerOrigin?_models original suffix same compatible

private noncomputable def Shared.Model.castOwners {left right : List (Context registry)}
    (same : left = right) (shared : Shared base left) (following : base.Realization)
    (reference : Tower.Model (Context.ofBase base) R)
    (model : Shared.Model shared following reference) :
    Shared.Model (_root_.cast (congrArg (Shared base) same) shared) following reference := by
  cases same
  exact model

/-- Collecting compatible original owners succeeds and preserves coherence
of the actual shared target, all returned maps, and all cached predecessors. -/
theorem Shared.Model.collect? {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    (model : Shared.Model shared following reference) (later : List (Context registry))
    (compatible : ∀ source ∈ later,
      source.origin.base.signature.constants <+: base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals) :
    ∃ result, shared.collect? later = some result ∧
      Nonempty (Shared.Model result following reference) := by
  induction later generalizing owners with
  | nil =>
    refine ⟨_, shared.collect?_nil, ⟨model.castOwners (List.append_nil owners).symm
      shared following reference⟩⟩
  | cons source rest ih =>
    obtain ⟨added, addedProduced, ⟨addedModel⟩⟩ :=
      model.add? source (compatible source (List.mem_cons_self ..))
    obtain ⟨result, resultProduced, ⟨resultModel⟩⟩ :=
      ih addedModel (fun source present => compatible source (List.mem_cons_of_mem _ present))
    refine ⟨_, ?_, ⟨resultModel.castOwners (List.append_assoc owners [source] rest)
      result following reference⟩⟩
    rw [Shared.collect?_cons, addedProduced]
    simp only [bind, Option.bind, resultProduced, pure]

/-- Gathering compatible native contexts constructs their interpretations and
cache coherence from one declared base model and its provider history. -/
theorem Shared.gather?_models (following : base.Realization)
    (reference : Tower.Model (Context.ofBase base) R) (owners : List (Context registry))
    (compatible : ∀ source ∈ owners,
      source.origin.base.signature.constants <+: base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals) :
    ∃ result, Shared.gather? base owners = some result ∧
      Nonempty (Shared.Model result following reference) := by
  rw [Shared.gather?_eq]
  exact (Shared.Model.empty following reference).collect? owners compatible

/-- Interpret an already returned native gathering result. The provider history
and native compatibility checks supply every owner and cache agreement. -/
noncomputable def Shared.Model.ofGather (following : base.Realization)
    (reference : Tower.Model (Context.ofBase base) R) (owners : List (Context registry))
    (shared : Shared base owners) (produced : Shared.gather? base owners = some shared) :
    Shared.Model shared following reference := Classical.choice (by
  obtain ⟨result, resultProduced, models⟩ :=
    Shared.gather?_models following reference owners
      (Shared.gather?_compatible base owners shared produced)
  have same := Option.some.inj (resultProduced.symm.trans produced)
  cases same
  exact models)

/-- Each retained value has its original owner's interpretation in the one
actual shared target. -/
theorem Shared.Model.value {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    (model : Shared.Model shared following reference)
    (index : Fin owners.length) (a : (owners[index]).Value) :
    model.target.value (shared.value index a) = (model.owners.get index).1.value a :=
  model.owners.value index a

/-- Interpret a gathered value using a separately retrieved canonical owner
model. Its agreement follows from the factory equations, even after `ofGather`. -/
theorem Shared.Model.value_of_model {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    (model : Shared.Model shared following reference)
    (index : Fin owners.length) (original : Tower.Model (owners[index]) R)
    (produced : (owners[index]).model? following reference = some original)
    (a : (owners[index]).Value) :
    model.target.value (shared.value index a) = original.value a := by
  have aligned := Option.some.inj ((model.canonicalOwners index).symm.trans produced)
  rw [model.value, aligned]

/-- Every transported polynomial uses the same original coefficient model. -/
theorem Shared.Model.polynomial {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    (model : Shared.Model shared following reference)
    (index : Fin owners.length) (p : (owners[index]).Poly) :
    HexPolyMathlib.Interpret.interpret model.target.value model.target.zero_iff
      (shared.polynomial index p) =
    HexPolyMathlib.Interpret.interpret (model.owners.get index).1.value
      (model.owners.get index).1.zero_iff p := model.owners.polynomial index p

/-- Gathering preserves every original owner's native sign. -/
theorem Shared.Model.sign {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    (model : Shared.Model shared following reference)
    (index : Fin owners.length) (a : (owners[index]).Value) :
    shared.input.context.sign (shared.value index a) = (owners[index]).sign a := by
  rw [model.target.sign, model.value, (model.owners.get index).1.sign]

/-- Gathering preserves all three original comparison results. -/
theorem Shared.Model.compare {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    (model : Shared.Model shared following reference)
    (index : Fin owners.length) (a b : (owners[index]).Value) :
    shared.input.context.compare (shared.value index a) (shared.value index b) =
      (owners[index]).compare a b := by
  rw [model.target.compare_spec, (model.owners.get index).1.compare_spec,
    model.value, model.value]

/-- The gathering factory supplies every agreement needed by actual shared
infinitesimal enlargement. All original owners enter its one returned ambient. -/
theorem Shared.Model.enlarge? {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    (model : Shared.Model shared following reference) (ambient : Ambient (Hex.RationalFn R)) :
    ∃ enlarged : SharedEnlargement shared,
      shared.enlarge? = some enlarged ∧
        ∃ inclusion : Inclusion.Model enlarged.previous (model.target.liftInfinitesimal ambient),
          inclusion.target.value enlarged.parameter = ambient.inclusion Hex.RationalFn.X ∧
          (∃ ownersModel : Inclusions.Models inclusion.target enlarged.shared.maps,
            ∀ index : Fin owners.length, (ownersModel.get index).1 =
              (model.owners.get index).1.liftInfinitesimal ambient) ∧
          ∀ (index : Fin owners.length) (a : (owners[index]).Value),
            inclusion.target.value (enlarged.shared.value index a) =
              Ambient.coefficientHom ambient ((model.owners.get index).1.value a) :=
  shared.enlarge?_models reference model.target model.owners ambient

private theorem Shared.enlargeOrigin_cache
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign) {owners : List (Context registry)}
    (shared : Shared (.pack base) owners) (suffix : Suffix (Context.base base))
    (same : suffix.context = shared.input.context)
    (rebuilt : Rebuilt (Conversion.infinitesimal base) suffix)
    (rebuiltEq : (Conversion.infinitesimal base).rebuild? suffix = some rebuilt)
    (result : SharedEnlargement shared)
    (produced : shared.enlargeOrigin? (Origin.pack base suffix same) = some result)
    (inputEq : result.shared.input = rebuilt.input.cast (Conversion.infinitesimal_spec base).1) :
    let nativeEq := rebuilt.context_eq.trans (rebuilt.input_spec.1.symm.trans
      (((rebuilt.input.cast_spec (Conversion.infinitesimal_spec base).1).1).symm.trans
        (congrArg Conversion.context inputEq.symm)))
    result.shared.cache =
      (nativeEq ▸ rebuilt.suffix.prefixes.cache).append (shared.cache.extend result.previous) := by
  simp only [Shared.enlargeOrigin?, rebuiltEq] at produced
  cases Option.some.inj produced
  simp only [SharedEnlargement.previous, Rebuilt.enlargement_conversion]

private theorem Shared.Model.enlargeOrigin
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign) {owners : List (Context registry)}
    {shared : Shared (.pack base) owners}
    {following : (BaseContext.PackedContext.pack base).Realization}
    {reference : Tower.Model (Context.base base) R}
    (model : Shared.Model shared following reference) (ambient : Ambient (Hex.RationalFn R))
    (suffix : Suffix (Context.base base)) (same : suffix.context = shared.input.context)
    (origin : shared.input.context.origin = Origin.pack base suffix same) :
    ∃ result : SharedEnlargement shared,
      shared.enlargeOrigin? (Origin.pack base suffix same) = some result ∧
        ∃ returned : Shared.Model result.shared following.infinitesimal
            (Tower.Model.nextBase base reference ambient),
          ∃ previous : Inclusion.Model result.previous (model.target.liftInfinitesimal ambient),
            previous.target = returned.target := by
  have restriction := restrict_model suffix same reference model.target
    (model.suffix base suffix same origin)
  obtain ⟨rebuilt, rebuiltEq, _, converted, convertedTarget⟩ :=
    Context.enlarge?_constructed base suffix same reference model.target ambient
  let input := Conversion.Model.infinitesimalMapped base (reference.baseHom base)
    (reference.baseHom_sign base) ambient
  have convertedAligned : HEq converted.target (input.target.extend rebuilt.suffix) := by
    have aligned := congrArg (fun original : Tower.Model (Context.base base) R =>
      (Conversion.Model.infinitesimalMapped base (original.baseHom base)
        (original.baseHom_sign base) ambient).target.extend rebuilt.suffix) restriction
    exact convertedTarget.trans (heq_of_eq aligned)
  have success : (shared.enlargeOrigin? (Origin.pack base suffix same)).isSome = true := by
    simp [Shared.enlargeOrigin?, rebuiltEq]
  let result := (shared.enlargeOrigin? (Origin.pack base suffix same)).get success
  have produced : shared.enlargeOrigin? (Origin.pack base suffix same) = some result :=
    (Option.some_get success).symm
  have checked : result.checked = rebuilt.enlargement base same := by
    simp [result, Shared.enlargeOrigin?, rebuiltEq]
  have checkedConversion : result.checked.conversion = rebuilt.result.cast same :=
    (congrArg Enlargement.conversion checked).trans (rebuilt.enlargement_conversion base same)
  let checkedModel : Conversion.Model result.checked.conversion
      (model.target.liftInfinitesimal ambient) := checkedConversion.symm ▸ converted
  let previous : Inclusion.Model result.previous (model.target.liftInfinitesimal ambient) :=
    ⟨checkedModel⟩
  have previousAligned : HEq previous.target (input.target.extend rebuilt.suffix) :=
    previous.target_heq.trans
      ((conversion_target_cast checkedConversion.symm converted).trans convertedAligned)
  let nextReference := Tower.Model.nextBase base reference ambient
  have inputCanonical : (Conversion.infinitesimal base).context.model?
      following.infinitesimal nextReference = some input.target :=
    model_produced_cast following.infinitesimal nextReference
      (Conversion.infinitesimal_spec base).1.symm nextReference input.target
      (Tower.Model.nextBase_target base reference ambient)
      (Context.model?_base following.infinitesimal nextReference)
  have inputEq : result.shared.input =
      rebuilt.input.cast (Conversion.infinitesimal_spec base).1 := by
    simp only [result, Shared.enlargeOrigin?, rebuiltEq, bind, Option.bind]
    rfl
  have nativeEq : rebuilt.suffix.context = result.shared.input.context :=
    rebuilt.context_eq.trans (rebuilt.input_spec.1.symm.trans
      (((rebuilt.input.cast_spec (Conversion.infinitesimal_spec base).1).1).symm.trans
        (congrArg Conversion.context inputEq.symm)))
  have canonical : result.shared.input.context.model? following.infinitesimal nextReference =
      some previous.target := model_produced_cast following.infinitesimal nextReference nativeEq
    (input.target.extend rebuilt.suffix) previous.target previousAligned
    (rebuilt.suffix.model?_extend following.infinitesimal nextReference input.target inputCanonical)
  let initialInput := input.rebuildInput suffix rebuilt
  let castInput := initialInput.cast (Conversion.infinitesimal_spec base).1
  have initialSource : (Conversion.infinitesimal_spec base).1 ▸ input.target = nextReference :=
    eq_of_heq ((input.target.cast_heq (Conversion.infinitesimal_spec base).1).trans
      (Tower.Model.nextBase_target base reference ambient))
  let finalInput : Conversion.Model result.shared.input nextReference :=
    inputEq.symm ▸ (initialSource ▸ castInput)
  have finalInputAligned : HEq finalInput.target previous.target :=
    (conversion_target_cast inputEq.symm (initialSource ▸ castInput)).trans
      ((model_target_cast initialSource castInput).trans
        ((initialInput.cast_target (Conversion.infinitesimal_spec base).1).trans
          ((input.rebuildInput_target suffix rebuilt).trans
            ((input.rebuild_target suffix rebuilt).trans previousAligned.symm))))
  have preserved : ∀ a, previous.target.value (result.shared.input.value a) =
      nextReference.value a := by
    intro a
    rw [← eq_of_heq finalInputAligned]
    exact finalInput.value a
  let liftedOwners := model.owners.map (Ambient.coefficientHom ambient)
    (Ambient.coefficientHom_strictMono ambient)
  let updatedOwners := liftedOwners.extend previous
  have mapsEq := shared.enlargeOrigin?_maps (Origin.pack base suffix same) result produced
  have family : ∃ ownersModel : Inclusions.Models previous.target result.shared.maps,
      ∀ index : Fin owners.length, (owners[index]).model? following.infinitesimal nextReference =
        some (ownersModel.get index).1 := by
    rw [mapsEq]
    refine ⟨updatedOwners, ?_⟩
    intro index
    have extended := Inclusions.Models.extend_original liftedOwners previous index
    have lifted := Inclusions.Models.map_original model.owners (Ambient.coefficientHom ambient)
      (Ambient.coefficientHom_strictMono ambient) index
    exact ((owners[index]).model?_next base following reference ambient
      (model.owners.get index).1 (model.canonicalOwners index)).trans
        (congrArg some (extended.trans lifted).symm)
  obtain ⟨ownersModel, ownersCanonical⟩ := family
  let nativeCache := cache_cast nativeEq following.infinitesimal nextReference
    (input.target.extend rebuilt.suffix) previous.target previousAligned
    rebuilt.suffix.prefixes.cache
    (rebuilt.suffix.prefixes_models following.infinitesimal nextReference input.target inputCanonical)
  let oldCache := model.cache.nextBase base following reference ambient result.previous
    previous.target previous.value
  have cacheEq : result.shared.cache =
      (nativeEq ▸ rebuilt.suffix.prefixes.cache).append (shared.cache.extend result.previous) := by
    exact shared.enlargeOrigin_cache base suffix same rebuilt rebuiltEq result produced inputEq
  have cacheModels : InclusionCache.Models following.infinitesimal nextReference previous.target
      result.shared.cache := by
    rw [cacheEq]
    exact nativeCache.append oldCache
  exact ⟨result, produced, ⟨previous.target, canonical, preserved, ownersModel, ownersCanonical,
    cacheModels⟩, previous, rfl⟩


/-- Enlarge the shared gathering and construct its complete canonical model.
The returned model retains original owners and a coherent predecessor cache,
so registration and further enlargement use the same factory afterwards. -/
theorem Shared.Model.enlarge {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    (model : Shared.Model shared following reference) (ambient : Ambient (Hex.RationalFn R)) :
    ∃ result : SharedEnlargement shared,
      shared.enlarge? = some result ∧
        ∃ returned : Shared.Model result.shared following.infinitesimal
            (Tower.Model.next base reference ambient),
          ∃ previous : Inclusion.Model result.previous (model.target.liftInfinitesimal ambient),
            previous.target = returned.target := by
  cases originEq : shared.input.context.origin with
  | pack original suffix same =>
    have originalEq : BaseContext.PackedContext.pack original = base :=
      (Suffix.origin_base original suffix).symm.trans
        ((congrArg (fun context => context.origin.base) same).trans shared.base_eq)
    cases originalEq
    obtain ⟨result, produced, returned, previous, aligned⟩ :=
      model.enlargeOrigin original ambient suffix same originEq
    refine ⟨result, ?_, ?_⟩
    · exact (congrArg shared.enlargeOrigin? originEq).trans produced
    · exact (Tower.Model.next_pack original reference ambient).symm ▸
        (⟨returned, previous, aligned⟩ : ∃ returned : Shared.Model result.shared
          following.infinitesimal (Tower.Model.nextBase original reference ambient),
          ∃ previous : Inclusion.Model result.previous (model.target.liftInfinitesimal ambient),
            previous.target = returned.target)

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Shared.gather?_models' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.gather?_models

/-- info: 'Hex.RealClosure.Tower.Shared.Model.compare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.Model.compare

/-- info: 'Hex.RealClosure.Tower.Shared.Model.ofGather' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.Model.ofGather
/-- info: 'Hex.RealClosure.Tower.Shared.Model.add?_transport' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.Model.add?_transport

/-- info: 'Hex.RealClosure.Tower.Shared.Model.register?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.Model.register?
/-- info: 'Hex.RealClosure.Tower.Shared.Model.enlarge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.Model.enlarge
