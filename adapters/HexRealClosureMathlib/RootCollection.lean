/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootCollection
public import HexRealClosureMathlib.RootTransport
public import HexRealClosureMathlib.TowerNaturality

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry} {parent target : Context registry} {K : Type u}
variable [Field K] [LinearOrder K] [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]

/-- The actual whole-root-context conversion agrees with the shared model. -/
structure RootMap.Model (entry : RootMap parent target) (original : Model parent K)
    (shared : Model target K) where
  converted : Conversion.Model entry.conversion (entry.source.model original)
  aligned : HEq converted.target shared

/-- Every transported value preserves its original root-context meaning. -/
theorem RootMap.Model.value {entry : RootMap parent target} {original : Tower.Model parent K}
    {shared : Tower.Model target K} (model : RootMap.Model entry original shared)
    (a : entry.source.context.Value) :
    shared.value (entry.apply a) = (entry.source.model original).value a := by
  rw [RootMap.apply, Tower.Model.value_cast entry.context model.converted.target shared
    model.aligned.symm, model.converted.value]

/-- The selected native root preserves its value in the shared context. -/
theorem RootMap.Model.root {entry : RootMap parent target} {original : Tower.Model parent K}
    {shared : Tower.Model target K} (model : RootMap.Model entry original shared) :
    shared.value entry.value = entry.source.denote original := model.value entry.source.value

omit [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K] in
private theorem cast_target {source : Context registry} {conversion : Conversion source}
    {left right : Tower.Model source K} (same : left = right)
    (model : Conversion.Model conversion right) :
    HEq (same.symm ▸ model).target model.target := by
  cases same
  rfl

/-- A later conversion carries each complete original root context into the
new target interpretation. -/
noncomputable def RootMap.Model.extend {entry : RootMap parent target}
    {original : Tower.Model parent K} {shared : Tower.Model target K}
    (model : RootMap.Model entry original shared) {next : Conversion target}
    (following : Conversion.Model next shared) :
    RootMap.Model (entry.extend next) original following.target := by
  rcases entry with ⟨source, conversion, same⟩
  cases same
  rcases model with ⟨converted, aligned⟩
  have equal : converted.target = shared := eq_of_heq aligned
  let continuation : Conversion.Model next converted.target := equal.symm ▸ following
  exact ⟨converted.comp continuation,
    (converted.comp_target continuation).trans (cast_target equal following)⟩

/-- A context equality and aligned actual shared model reconcile target
ownership without changing any original source interpretation. -/
noncomputable def RootMap.Model.retarget {entry : RootMap parent target}
    {original : Tower.Model parent K} {shared : Tower.Model target K}
    (model : RootMap.Model entry original shared) {other : Context registry}
    (same : target = other) (actual : Tower.Model other K) (aligned : HEq actual shared) :
    RootMap.Model (entry.cast same) original actual := by
  cases same
  exact ⟨model.converted, model.aligned.trans aligned.symm⟩

/-- A shared collection preserves its coefficient context and every complete
original root context in one compatible ambient interpretation. -/
structure Collection.Model (collection : Collection parent) (original : Model parent K) where
  input : Conversion.Model collection.input original
  entries : ∀ entry ∈ collection.entries, Nonempty (RootMap.Model entry original input.target)

/-- The empty collection uses the actual identity coefficient conversion. -/
noncomputable def Collection.Model.empty (original : Tower.Model parent K) :
    Collection.Model (Collection.empty parent) original where
  input := Conversion.Model.identity original
  entries := fun _ member => False.elim (List.not_mem_nil member)

/-- Adding an actually moved root transports all existing root contexts
before recording the new root's complete source inclusion. -/
noncomputable def Collection.Model.add {collection : Collection parent}
    {original : Tower.Model parent K} (model : Collection.Model collection original)
    {source : Root parent} {moved : Moved collection.input source}
    (witness : Moved.Model moved original model.input) :
    Collection.Model (collection.add source moved) original := by
  let combined := model.input.comp witness.input
  let same := (collection.input.comp_spec moved.input).1.symm
  refine ⟨combined, ?_⟩
  intro entry member
  change entry ∈ (collection.entries.map
    (fun previous => (previous.extend moved.input).cast same)) ++ [_] at member
  rcases List.mem_append.mp member with previous | newest
  · obtain ⟨oldEntry, present, rfl⟩ := List.mem_map.mp previous
    obtain ⟨preserved⟩ := model.entries oldEntry present
    exact ⟨(preserved.extend witness.input).retarget same combined.target
      (model.input.comp_target witness.input)⟩
  · have equal := List.mem_singleton.mp newest
    subst entry
    exact ⟨⟨witness.transported, witness.transported_target.trans
      ((model.input.comp_target witness.input).trans witness.input_target).symm⟩⟩

/-- The shared-context producer succeeds at every finite number of roots,
preserving the original coefficient and whole-root-context interpretations. -/
theorem Collection.gather?_success {collection : Collection parent}
    {original : Tower.Model parent K} (model : Collection.Model collection original)
    (sources : List (Root parent)) :
    ∃ result, collection.gather? sources = some result ∧
      Nonempty (Collection.Model result original) := by
  induction sources generalizing collection with
  | nil => exact ⟨collection, rfl, ⟨model⟩⟩
  | cons source rest ih =>
    obtain ⟨moved, produced, witness⟩ := source.move?_success model.input
    obtain ⟨witness⟩ := witness
    obtain ⟨result, returned, preserved⟩ := ih (model.add witness)
    exact ⟨result, by simp only [Collection.gather?, produced]; exact returned,
      preserved⟩

/-- Actual complete collection from the original immutable parent succeeds. -/
theorem Context.collect?_success (original : Model parent K) (sources : List (Root parent)) :
    ∃ result, parent.collect? sources = some result ∧ Nonempty (Collection.Model result original) :=
  Collection.gather?_success (Collection.Model.empty original) sources

/-- All collected values denote the original roots in their retained order. -/
theorem Collection.Model.values {collection : Collection parent} {original : Tower.Model parent K}
    (model : Collection.Model collection original) :
    collection.values.map model.input.target.value =
      collection.sources.map (fun root => root.denote original) := by
  simp only [Collection.values, Collection.sources, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro entry member
  obtain ⟨preserved⟩ := model.entries entry member
  exact preserved.root

/-- Ordinary collection is the actual successful checked result and retains
the complete source-context interpretation witnesses. -/
theorem Context.collect_success (original : Model parent K) (sources : List (Root parent)) :
    parent.collect? sources = some (parent.collect sources) ∧
      Nonempty (Collection.Model (parent.collect sources) original) := by
  obtain ⟨result, returned, preserved⟩ := Context.collect?_success original sources
  simpa only [Context.collect, returned] using And.intro returned preserved

/-- Ordinary collection preserves the complete list of original root handles. -/
theorem Context.collect_sources (original : Model parent K) (sources : List (Root parent)) :
    (parent.collect sources).sources = sources :=
  Context.collect?_sources sources (parent.collect sources)
    (Context.collect_success original sources).1

/-- Strict ordering of the original roots is retained by values in the shared
context, using actual arithmetic in its single compatible model. -/
theorem Collection.Model.sorted {collection : Collection parent} {original : Tower.Model parent K}
    (model : Collection.Model collection original)
    (ordered : (collection.sources.map (fun root => root.denote original)).Pairwise (· < ·)) :
    (collection.values.map model.input.target.value).Pairwise (· < ·) := by
  rw [model.values]
  exact ordered

/-- The complete native root producer can use one shared arithmetic context
while retaining the strict order of all its returned roots. -/
theorem Context.roots_collected_sorted (original : Model parent K) (p : DensePoly parent.Value)
    {entries : List (RootEntry parent)} (returned : parent.roots p = .finite entries) :
    let collection := parent.collect (entries.map (·.root))
    ∀ model : Collection.Model collection original,
      (collection.values.map model.input.target.value).Pairwise (· < ·) := by
  intro collection model
  apply model.sorted
  rw [Context.collect_sources original]
  simpa only [List.map_map, Function.comp_def, RootEntry.denote] using
    Context.roots_sorted original p returned

/-- Native sign comparisons strictly order the complete roots in their
single collected arithmetic context. -/
theorem Context.roots_collected_ordered (original : Model parent K) (p : DensePoly parent.Value)
    {entries : List (RootEntry parent)} (returned : parent.roots p = .finite entries) :
    let collection := parent.collect (entries.map (·.root))
    collection.values.Pairwise (fun a b => collection.input.context.sign (b - a) = 1) := by
  intro collection
  obtain ⟨model⟩ := (Context.collect_success original (entries.map (·.root))).2
  have ordered := Context.roots_collected_sorted original p returned model
  rw [List.pairwise_map] at ordered
  apply ordered.imp
  intro a b less
  rw [model.input.target.sign, model.input.target.sub, sign_eq_one_iff.mpr (sub_pos.mpr less)]
  rfl

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.RootMap.Model.value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.RootMap.Model.value

/-- info: 'Hex.RealClosure.Tower.RootMap.Model.extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.RootMap.Model.extend

/-- info: 'Hex.RealClosure.Tower.Context.collect?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Context.collect?_success

/-- info: 'Hex.RealClosure.Tower.Context.collect_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Context.collect_success

/-- info: 'Hex.RealClosure.Tower.Collection.Model.values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Collection.Model.values

/-- info: 'Hex.RealClosure.Tower.Context.roots_collected_sorted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Context.roots_collected_sorted

/-- info: 'Hex.RealClosure.Tower.Context.roots_collected_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.roots_collected_ordered
