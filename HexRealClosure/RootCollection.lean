/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootTransport

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry} {parent : Context registry}

/-- An inclusion of an entire original root context into a shared target.
The source root retains its original ownership and selection evidence. -/
structure RootMap (parent target : Context registry) : Type 1 where
  source : Root parent
  conversion : Conversion source.context
  context : conversion.context = target

/-- Transport any original root-context value into the shared context. -/
@[expose] def RootMap.apply {target : Context registry} (entry : RootMap parent target)
    (a : entry.source.context.Value) : target.Value :=
  _root_.cast (congrArg Context.Value entry.context) (entry.conversion.value a)

/-- The selected root as a value of the shared target context. -/
@[expose] def RootMap.value {target : Context registry} (entry : RootMap parent target) :
    target.Value := entry.apply entry.source.value

/-- Reconcile target ownership along a proved context equality. -/
@[expose] def RootMap.cast {target other : Context registry} (entry : RootMap parent target)
    (same : target = other) : RootMap parent other := same ▸ entry

/-- Include all original root-context values through one later conversion. -/
@[expose] def RootMap.extend {target : Context registry} (entry : RootMap parent target)
    (next : Conversion target) : RootMap parent next.context :=
  let following := next.cast entry.context.symm
  ⟨entry.source, entry.conversion.comp following,
    (entry.conversion.comp_spec following).1.trans (next.cast_spec entry.context.symm).1⟩

/-- A shared native context, its original coefficient inclusion, and the
ordered inclusions of all roots collected so far. -/
structure Collection (parent : Context registry) : Type 1 where
  input : Conversion parent
  entries : List (RootMap parent input.context)

/-- Begin in the original immutable coefficient context. -/
@[expose] def Collection.empty (parent : Context registry) : Collection parent :=
  ⟨Conversion.identity parent, []⟩

/-- Original root handles in their retained input order. -/
@[expose] def Collection.sources (collection : Collection parent) : List (Root parent) :=
  collection.entries.map (·.source)

/-- The roots as ordinary native values in one shared arithmetic context. -/
@[expose] def Collection.values (collection : Collection parent) : List collection.input.context.Value :=
  collection.entries.map (·.value)

/-- Add one actually moved root, embedding all previously collected contexts
through its new coefficient inclusion. -/
@[expose] def Collection.add (collection : Collection parent) (source : Root parent)
    (moved : Moved collection.input source) : Collection parent :=
  let combined := collection.input.comp moved.input
  let same := (collection.input.comp_spec moved.input).1.symm
  let previous := collection.entries.map (fun entry => (entry.extend moved.input).cast same)
  let newest : RootMap parent combined.context :=
    ⟨source, moved.transported,
      moved.transported_context.trans (moved.input_context.symm.trans same)⟩
  ⟨combined, previous ++ [newest]⟩

/-- Checked shared-context assembly; each later root is revalidated over the
current converted coefficients. -/
@[expose] def Collection.gather? (collection : Collection parent) :
    List (Root parent) → Option (Collection parent)
  | [] => some collection
  | source :: rest => do
    let moved ← source.move? collection.input
    (collection.add source moved).gather? rest

/-- Gather root handles into one context with maps for every original value. -/
@[expose] def Context.collect? (parent : Context registry) (sources : List (Root parent)) :
    Option (Collection parent) := (Collection.empty parent).gather? sources

/-- Ordinary shared-context assembly. The companion proves the diagnostic
failure branch unreachable under the coefficient model laws. -/
@[expose] def Context.collect (parent : Context registry) (sources : List (Root parent)) :
    Collection parent :=
  match parent.collect? sources with
  | some collection => collection
  | none =>
    letI : Inhabited (Collection parent) := ⟨Collection.empty parent⟩
    panic! "Tower.Context.collect: root revalidation failed"

theorem RootMap.cast_source {target other : Context registry} (entry : RootMap parent target)
    (same : target = other) : (entry.cast same).source = entry.source := by
  cases same
  rfl

theorem Collection.add_sources (collection : Collection parent) (source : Root parent)
    (moved : Moved collection.input source) :
    (collection.add source moved).sources = collection.sources ++ [source] := by
  simp only [Collection.add, Collection.sources, List.map_append, List.map_map,
    List.map_cons, List.map_nil, Function.comp_def, RootMap.cast_source, RootMap.extend]

/-- Assembly retains every source root exactly once and in input order. -/
theorem Collection.gather?_sources (collection : Collection parent)
    (sources : List (Root parent)) (result : Collection parent)
    (returned : collection.gather? sources = some result) :
    result.sources = collection.sources ++ sources := by
  induction sources generalizing collection with
  | nil =>
    have same : collection = result := Option.some.inj returned
    simp only [same, List.append_nil]
  | cons source rest ih =>
    simp only [Collection.gather?] at returned
    cases produced : source.move? collection.input with
    | none => simp [produced] at returned
    | some moved =>
      simp only [produced] at returned
      rw [ih _ returned, Collection.add_sources, List.append_assoc]
      rfl

theorem Context.collect?_sources (sources : List (Root parent)) (result : Collection parent)
    (returned : parent.collect? sources = some result) : result.sources = sources := by
  simpa only [Context.collect?, Collection.sources, Collection.empty, List.map_nil,
    List.nil_append] using (Collection.empty parent).gather?_sources sources result returned

end Hex.RealClosure.Tower
