/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseSubsequenceTests
public import HexRealClosureMathlib.CacheGather
public import HexRealClosure.SharedPresentation
public import HexRealClosure.SharedBase
public import HexRealClosureMathlib.LiveRequest

public section

namespace Hex.RealClosure.BaseContext.SubsequenceTests

open OrderedFn OrderedFn.Oracle

/-- The shared factory rebuilds a complete algebraic suffix over `[β]` in the
actual registered `[α, β]` target, retaining its earlier infinitesimals. Only the
target's provider realization is passed to model derivation. -/
theorem gather_insert_before {registry : Registry} (source parent : RealPrefix.Model registry)
    (α β : ConstantKey) (sourceKeys : source.context.keys = [β])
    (parentKeys : parent.context.keys = [α])
    (present : (registry β).isSome = true) (τ : ℝ)
    (contained : ∀ δ, 0 < δ → Contains ((registry β).get present δ) τ)
    (width : ∀ δ, 0 < δ → ((registry β).get present δ).width ≤ δ)
    (transcendental : letI : Field parent.context.Carrier := HexPolyMathlib.fieldOfGrind
      Real.RelativeTranscendence parent.interpretation.hom τ)
    (n m : Nat) (depth : n ≤ m)
    (suffix : Tower.Suffix (Tower.Context.ofBase (source.context.finish.extend n))) :
    let child := parent.register β present τ contained width transcendental
    let base := child.context.finish.extend m
    let following := child.staged m
    let reference := following.reference.model
    ∃ shared, Tower.Shared.gather? base [suffix.context] = some shared ∧
      Nonempty (Tower.Shared.Model shared following reference) := by
  intro child base following reference
  apply Tower.Shared.gather?_models following reference [suffix.context]
  intro owner member
  have same : owner = suffix.context := by simpa only [List.mem_singleton] using member
  subst owner
  rw [Tower.Suffix.base_eq, Tower.Context.ofBase_origin_base]
  simp only [base, PackedContext.extend_signature, RealPrefix.finish_signature]
  constructor
  · rw [sourceKeys, RealPrefix.Model.register_keys, parentKeys]
    exact List.sublist_append_right [α] [β]
  · simpa only [Nat.zero_add] using depth

private theorem catalog_model {registry : Registry} (provider : RealPrefix.Model registry)
    (catalog : Catalog registry)
    (installed : (Catalog.empty registry).insert provider.context = some catalog)
    (candidate : RealPrefix registry) (member : candidate ∈ catalog.prefixes) :
    ∃ model : RealPrefix.Model registry, model.context = candidate := by
  rcases (Catalog.mem_prefixes_of_insert (Catalog.empty registry) catalog
    provider.context candidate installed).mp member with same | earlier
  · exact ⟨provider, same.symm⟩
  · rw [Catalog.prefixes_empty] at earlier
    have same := List.mem_singleton.mp earlier
    refine ⟨RealPrefix.Model.rational registry, ?_⟩
    rw [same]
    exact RealPrefix.Model.rational_context registry

/-- One installed provider model supplies the interpretation of the actual
automatically chosen target, including its infinitesimal suffix and every
gathered owner. No target realization or ambient model is supplied separately. -/
theorem gather_catalog {registry : Registry} (provider : RealPrefix.Model registry)
    (catalog : Catalog registry)
    (installed : (Catalog.empty registry).insert provider.context = some catalog)
    (owners : List (Tower.Context registry)) (base : PackedContext registry)
    (shared : Tower.Shared base owners)
    (accepted : Tower.Shared.gatherFrom? catalog owners = some ⟨base, shared⟩) :
    ∃ following : base.Realization,
      Nonempty (Tower.Shared.Model shared following following.reference.model) := by
  have produced := Tower.Shared.gatherFrom?_gathered catalog owners base shared accepted
  obtain ⟨candidate, member, target⟩ :=
    Tower.Shared.gatherFrom?_base catalog owners base shared accepted
  obtain ⟨model, modeled⟩ := catalog_model provider catalog installed candidate member
  rw [← modeled] at target
  subst base
  let following := model.staged (Tower.SharedBase.depth (owners.map (·.origin.base)))
  exact ⟨following, ⟨Tower.Shared.Model.ofGather following following.reference.model
    owners shared produced⟩⟩

/-- The same installed provider model interprets an automatically gathered
live request, including its actual transported values, polynomials and roots. -/
theorem gather_catalog_request {registry : Registry} (provider : RealPrefix.Model registry)
    (catalog : Catalog registry)
    (installed : (Catalog.empty registry).insert provider.context = some catalog)
    (request : Tower.Live.Request registry) (base : PackedContext registry)
    (collection : Tower.Live.Collection base request)
    (accepted : request.gatherFrom? catalog = some ⟨base, collection⟩) :
    ∃ following : base.Realization,
      Nonempty (Tower.Shared.Model collection.shared following following.reference.model) := by
  have produced := Tower.Live.Request.gatherFrom?_gathered catalog request base collection accepted
  obtain ⟨candidate, member, target⟩ :=
    Tower.Live.Request.gatherFrom?_base catalog request base collection accepted
  obtain ⟨model, modeled⟩ := catalog_model provider catalog installed candidate member
  rw [← modeled] at target
  subst base
  let following := model.staged (Tower.SharedBase.depth (request.owners.map (·.origin.base)))
  exact ⟨following, ⟨collection.model following following.reference.model produced⟩⟩

end Hex.RealClosure.BaseContext.SubsequenceTests

/-- info: 'Hex.RealClosure.BaseContext.SubsequenceTests.gather_insert_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.SubsequenceTests.gather_insert_before

/-- info: 'Hex.RealClosure.BaseContext.Catalog.mem_prefixes_of_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.Catalog.mem_prefixes_of_insert

/-- info: 'Hex.RealClosure.BaseContext.SubsequenceTests.gather_catalog' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.SubsequenceTests.gather_catalog

/-- info: 'Hex.RealClosure.BaseContext.SubsequenceTests.gather_catalog_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.SubsequenceTests.gather_catalog_request
