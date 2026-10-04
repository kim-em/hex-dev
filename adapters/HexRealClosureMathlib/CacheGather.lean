/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.CacheRebuild

public section

namespace Hex.RealClosure.Tower

open scoped Hex.OrderedFn.Infinitesimal

variable {registry : BaseContext.Registry} {base : BaseContext.PackedContext registry}
variable {R : Type u} [Field R] [LinearOrder R] [DecidableEq R]
variable [IsStrictOrderedRing R] [IsRealClosed R]

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

private theorem nil_heq {left right : Context registry} (same : left = right) :
    HEq (Inclusions.nil (target := left)) (Inclusions.nil (target := right)) := by
  cases same
  rfl

private theorem cache_empty_heq {left right : Context registry} (same : left = right)
    (cache : InclusionCache left) (empty : cache.entries = []) :
    HEq cache (⟨[]⟩ : InclusionCache right) := by
  cases same
  cases cache
  cases empty
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
      (⟨[]⟩ : InclusionCache conversion.context) :=
    cache_empty_heq contextEq _ (Shared.empty_entries base)
  exact Shared.Model.ofParts (Shared.empty base) following reference conversion same
    model.target canonical model.value .nil mapsEq .nil (fun index => nomatch index) ⟨[]⟩ cacheEq
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
  obtain ⟨result, resultProduced, inputEq, mapsEq, cacheEq⟩ :=
    shared.addOrigin?_spec original suffix same previous baseProduced rebuilt rebuiltProduced
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
  exact ⟨result, resultProduced, ⟨Shared.Model.ofParts result following reference
    combined inputEq interpreted.target canonical preserved _ mapsEq ownersModel canonicalOwners
    rebuilt.cache cacheEq interpreted.cache⟩⟩

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
    (compatible : ∀ source ∈ owners,
      source.origin.base.signature.constants <+: base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals)
    (shared : Shared base owners) (produced : Shared.gather? base owners = some shared) :
    Shared.Model shared following reference := Classical.choice (by
  obtain ⟨result, resultProduced, models⟩ :=
    Shared.gather?_models following reference owners compatible
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

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Shared.gather?_models' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.gather?_models

/-- info: 'Hex.RealClosure.Tower.Shared.Model.compare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.Model.compare
