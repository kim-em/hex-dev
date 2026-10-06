/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.CacheModels

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry} {base : BaseContext.PackedContext registry}
variable {R : Type u} [Field R] [LinearOrder R] [DecidableEq R]
variable [IsStrictOrderedRing R] [IsRealClosed R]
variable {reader : OwnerReader registry R}

/-- The actual rebuilt target and every retained original owner are
interpreted in one field. The target is the canonical owner-factory result,
and its predecessor inclusion preserves all values in the old target. -/
structure CacheResult.Model {previous original : Context registry}
    (result : CacheResult previous original) (following : base.Realization)
    (reference : Tower.Model (Context.ofBase base) R) (old : Tower.Model previous R)
    (reader : OwnerReader registry R := OwnerReader.ordered following reference) where
  target : Tower.Model result.target R
  produced : reader.read result.target = some target
  previous : ∀ a, target.value (result.inclusion.value a) = old.value a
  original : InclusionCache.EntryModel (reader := reader) following reference target result.original
  cache : InclusionCache.Models (reader := reader) following reference target result.cache

/-- Rebuilding a compatible canonical owner always succeeds. Every cache hit
retains that owner's interpretation, and every new root extends the fixed
canonical target while preserving all prior cache entries. -/
theorem InclusionCache.rebuild?_models {source destination : Context registry}
    (following : base.Realization) (reference : Tower.Model (Context.ofBase base) R)
    (cache : InclusionCache destination) (target : Tower.Model destination R)
    (models : InclusionCache.Models (reader := reader) following reference target cache)
    (canonical : reader.read destination = some target)
    (initial : Inclusion source destination)
    (incoming : InclusionCache.EntryModel (reader := reader) following reference target initial)
    (suffix : Suffix source) :
    ∃ result, cache.rebuild? initial suffix = some result ∧
      Nonempty (result.Model (reader := reader) following reference target) := by
  induction suffix generalizing destination with
  | nil =>
    refine ⟨⟨destination, Inclusion.identity destination, initial, cache, rfl⟩,
      rfl, ⟨⟨target, canonical, ?_, incoming, models⟩⟩⟩
    intro a
    rw [Inclusion.identity_value]
  | @root source descriptor rest ih =>
    cases hit : cache.find? (source.adjoin descriptor).context with
    | some found =>
      let cached := models.get found hit
      obtain ⟨result, produced, ⟨interpreted⟩⟩ := ih cache target models canonical found cached
      refine ⟨result, ?_, ⟨interpreted⟩⟩
      rw [cache.rebuild?_hit initial descriptor rest found hit]
      exact produced
    | none =>
      have success : ∃ converted : SignDet.Descriptor destination.Value Signature
          destination.sign destination.signature,
          SignDet.Descriptor.validate destination.sign destination.signature
            (source.mapDescriptor destination initial.value descriptor) = some converted :=
        incoming.native.descriptor_exists descriptor
      obtain ⟨converted, checked⟩ := success
      cases matched : cache.findRoot? converted with
      | some existing =>
        let binding := SignDet.Descriptor.build_raw
          (SignDet.Descriptor.validate_eq_some.mp checked)
        let next := initial.reuseRoot descriptor converted binding existing
        let nextEntry := incoming.reuseRoot descriptor converted binding existing
        let updated := cache.insert next
        let updatedModels := models.insert next nextEntry
        obtain ⟨result, produced, ⟨interpreted⟩⟩ :=
          ih updated target updatedModels canonical next nextEntry
        refine ⟨result, ?_, ⟨interpreted⟩⟩
        rw [cache.rebuild?_reuse initial descriptor rest hit converted checked existing matched]
        exact produced
      | none =>
        let child := destination.adjoin converted
        let previous : Inclusion destination child.context :=
          ⟨Conversion.includeRoot destination converted child rfl,
            (Conversion.includeRoot_spec destination converted child rfl).1⟩
        let next : Inclusion (source.adjoin descriptor).context child.context :=
          ⟨initial.native.adjoinCached descriptor converted checked child rfl,
            (initial.native.adjoinCached_spec descriptor converted checked child rfl).1⟩
        let nextTarget := target.adjoin converted
        have nextCanonical : reader.read child.context = some nextTarget := by
          change reader.read (destination.adjoin converted).context =
            some (target.adjoin converted)
          rw [reader.adjoin, canonical, Option.map_some]
        let previousModel : Inclusion.Model previous target :=
          ⟨Conversion.Model.includeRoot target converted child rfl⟩
        have aligned : previousModel.target = nextTarget :=
          eq_of_heq (previousModel.target_heq.trans
            (Conversion.Model.includeRoot_target target converted child rfl))
        have previousValue : ∀ a, nextTarget.value (previous.value a) = target.value a := by
          intro a
          rw [← aligned]
          exact previousModel.value a
        let nextEntry : InclusionCache.EntryModel (reader := reader) following reference nextTarget next :=
          incoming.adjoin descriptor converted checked
        let updated := ((cache.extend previous).insert next).insert (Inclusion.identity child.context)
        let updatedModels : InclusionCache.Models (reader := reader) following reference nextTarget updated :=
          ((models.transport previous nextTarget previousValue).insert next nextEntry).insert
            (Inclusion.identity child.context)
            (InclusionCache.EntryModel.identity nextTarget nextCanonical)
        obtain ⟨later, laterProduced, ⟨laterModel⟩⟩ :=
          ih updated nextTarget updatedModels nextCanonical next nextEntry
        let result : CacheResult destination rest.context :=
          ⟨later.target, previous.comp later.inclusion, later.original, later.cache,
            later.base_eq.trans (by
              change (destination.adjoin converted).context.origin.base = destination.origin.base
              rw [Context.origin_adjoin, Origin.snoc_base])⟩
        refine ⟨result, ?_, ⟨⟨laterModel.target, laterModel.produced, ?_,
          laterModel.original, laterModel.cache⟩⟩⟩
        · rw [cache.rebuild?_miss initial descriptor rest hit converted checked matched]
          change (updated.rebuild? next rest).map _ = some result
          rw [laterProduced]
          rfl
        · intro a
          rw [Inclusion.comp_value, laterModel.previous, previousValue]

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.InclusionCache.rebuild?_models' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.InclusionCache.rebuild?_models
