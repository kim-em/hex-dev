/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.LiveRequest

public section
namespace Hex.RealClosure.Tower
variable {registry : BaseContext.Registry}

/-- One common validated base with a checked inclusion for every original
base. Sources retain their immutable owners and original coefficient types. -/
structure SharedBase (sources : List (BaseContext.PackedContext registry)) : Type 1 where
  target : BaseContext.PackedContext registry
  included : ∀ source ∈ sources, (Inclusion.base? source target).isSome = true

/-- Retrieve the actual checked native inclusion for an original base. -/
def SharedBase.inclusion {sources : List (BaseContext.PackedContext registry)}
    (shared : SharedBase sources) (source : BaseContext.PackedContext registry)
    (member : source ∈ sources) : Inclusion (Context.ofBase source) (Context.ofBase shared.target) :=
  (Inclusion.base? source shared.target).get (shared.included source member)

/-- The largest requested infinitesimal depth suffices for all original bases. -/
@[expose] def SharedBase.depth (sources : List (BaseContext.PackedContext registry)) : Nat :=
  sources.foldl (fun depth source => max depth source.depth) 0

private theorem fold_depth (sources : List (BaseContext.PackedContext registry))
    (initial : Nat) : initial ≤ sources.foldl (fun depth source => max depth source.depth) initial := by
  induction sources generalizing initial with
  | nil => exact Nat.le_refl initial
  | cons first rest ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem fold_member (sources : List (BaseContext.PackedContext registry))
    (initial : Nat) (source : BaseContext.PackedContext registry) (member : source ∈ sources) :
    source.depth ≤ sources.foldl (fun depth source => max depth source.depth) initial := by
  induction sources generalizing initial with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst source
      exact Nat.le_trans (Nat.le_max_right _ _) (fold_depth rest _)
    · exact ih (max initial first.depth) later

/-- The selected depth retains every requested infinitesimal predecessor. -/
theorem SharedBase.depth_bound (sources : List (BaseContext.PackedContext registry))
    (source : BaseContext.PackedContext registry) (member : source ∈ sources) :
    source.depth ≤ SharedBase.depth sources := fold_member sources 0 source member

/-- Choose the first installed validated prefix whose actual native base
includes all requests. Add the maximum requested infinitesimal depth. This
search does not manufacture relative-transcendence or convergence premises. -/
def SharedBase.choose? (catalog : BaseContext.Catalog registry)
    (sources : List (BaseContext.PackedContext registry)) : Option (SharedBase sources) :=
  let allowed := fun candidate : BaseContext.RealPrefix registry =>
    sources.all (fun source => (Inclusion.base? source (candidate.finish.extend (depth sources))).isSome)
  match selected : catalog.prefixes.find? allowed with
  | none => none
  | some candidate => some ⟨candidate.finish.extend (depth sources), by
      have accepted : sources.all (fun source =>
          (Inclusion.base? source (candidate.finish.extend (depth sources))).isSome) = true :=
        List.find?_some (p := allowed) (a := candidate) (l := catalog.prefixes) selected
      exact List.all_eq_true.mp accepted⟩

/-- The catalog search succeeds exactly when one installed validated prefix
admits all original bases through the native inclusion checker. -/
theorem SharedBase.choose?_isSome (catalog : BaseContext.Catalog registry)
    (sources : List (BaseContext.PackedContext registry)) :
    (SharedBase.choose? catalog sources).isSome = true ↔
      ∃ candidate ∈ catalog.prefixes, ∀ source ∈ sources,
        (Inclusion.base? source (candidate.finish.extend (depth sources))).isSome = true := by
  have agrees : (SharedBase.choose? catalog sources).isSome =
      (catalog.prefixes.find? (fun candidate => sources.all (fun source =>
        (Inclusion.base? source (candidate.finish.extend (depth sources))).isSome))).isSome := by
    unfold choose?
    dsimp only
    split <;> simp_all only [Option.isSome_none, Option.isSome_some]
  rw [agrees]
  simp only [List.find?_isSome, List.all_eq_true]

/-- A catalog containing a jointly validated real prefix suffices. The source
bases may be incomparable; no caller-selected target or depth is required. -/
theorem SharedBase.choose?_success (catalog : BaseContext.Catalog registry)
    (sources : List (BaseContext.PackedContext registry))
    (candidate : BaseContext.RealPrefix registry) (installed : candidate ∈ catalog.prefixes)
    (keys : ∀ source ∈ sources, List.Sublist source.signature.constants candidate.keys) :
    (SharedBase.choose? catalog sources).isSome = true := by
  apply (SharedBase.choose?_isSome catalog sources).mpr
  refine ⟨candidate, installed, ?_⟩
  intro source member
  apply (Inclusion.base?_isSome source _).mpr
  simp only [BaseContext.PackedContext.extend_signature, BaseContext.RealPrefix.finish_signature,
    BaseContext.PackedContext.depth, Nat.zero_add]
  exact ⟨keys source member, SharedBase.depth_bound sources source member⟩

/-- Every retained source inclusion uses the full ordered real-key path and
preserves its infinitesimal predecessors. -/
theorem SharedBase.compatible {sources : List (BaseContext.PackedContext registry)}
    (shared : SharedBase sources) (source : BaseContext.PackedContext registry)
    (member : source ∈ sources) :
    List.Sublist source.signature.constants shared.target.signature.constants ∧
      source.depth ≤ shared.target.depth :=
  (Inclusion.base?_isSome source shared.target).mp (shared.included source member)

/-- Select a common catalog base before rebuilding complete owner ancestry.
The returned shared context retains all original owner maps and its cache. -/
@[expose] def Shared.gatherFrom? (catalog : BaseContext.Catalog registry)
    (owners : List (Context registry)) : Option (Σ base, Shared base owners) := do
  let chosen ← SharedBase.choose? catalog (owners.map (·.origin.base))
  let shared ← Shared.gather? chosen.target owners
  return ⟨chosen.target, shared⟩

/-- Successful selection and gathering retain exactly the chosen shared context. -/
theorem Shared.gatherFrom?_of_success (catalog : BaseContext.Catalog registry)
    (owners : List (Context registry)) (chosen : SharedBase (owners.map (·.origin.base)))
    (selected : SharedBase.choose? catalog (owners.map (·.origin.base)) = some chosen)
    (shared : Shared chosen.target owners) (gathered : Shared.gather? chosen.target owners = some shared) :
    Shared.gatherFrom? catalog owners = some ⟨chosen.target, shared⟩ := by
  simp only [Shared.gatherFrom?, selected, gathered, bind, Option.bind, pure]

/-- Select the base, gather every original dependency, and transport all requested
values, polynomials and descriptors through the resulting owner maps. -/
@[expose] def Live.Request.gatherFrom? (catalog : BaseContext.Catalog registry)
    (request : Live.Request registry) : Option (Σ base, Live.Collection base request) := do
  let chosen ← SharedBase.choose? catalog (request.owners.map (·.origin.base))
  let collection ← request.gather? chosen.target
  return ⟨chosen.target, collection⟩

/-- The request factory returns the existing checked collection unchanged. -/
theorem Live.Request.gatherFrom?_of_success (catalog : BaseContext.Catalog registry)
    (request : Live.Request registry) (chosen : SharedBase (request.owners.map (·.origin.base)))
    (selected : SharedBase.choose? catalog (request.owners.map (·.origin.base)) = some chosen)
    (collection : Live.Collection chosen.target request)
    (gathered : request.gather? chosen.target = some collection) :
    request.gatherFrom? catalog = some ⟨chosen.target, collection⟩ := by
  simp only [Live.Request.gatherFrom?, selected, gathered, bind, Option.bind, pure]

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.SharedBase.choose?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.SharedBase.choose?_isSome

/-- info: 'Hex.RealClosure.Tower.SharedBase.compatible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.SharedBase.compatible

/-- info: 'Hex.RealClosure.Tower.SharedBase.depth_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.SharedBase.depth_bound
/-- info: 'Hex.RealClosure.Tower.SharedBase.choose?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.SharedBase.choose?_success
/-- info: 'Hex.RealClosure.Tower.Shared.gatherFrom?_of_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.gatherFrom?_of_success
/-- info: 'Hex.RealClosure.Tower.Live.Request.gatherFrom?_of_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Request.gatherFrom?_of_success
