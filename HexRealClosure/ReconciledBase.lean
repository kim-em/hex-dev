/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.SharedBase
public import HexRealClosure.ReconciledLive

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry}

/-- A common validated target for provider-key reconciliation. Selection checks
only key distinctness and containment; coefficient maps are built by gathering. -/
structure SharedBase.Reconciled (sources : List (BaseContext.PackedContext registry)) : Type 1 where
  target : BaseContext.PackedContext registry
  distinct : target.signature.constants.Nodup
  included : ∀ source ∈ sources, source.signature.constants.Nodup ∧
    source.signature.constants ⊆ target.signature.constants ∧ source.depth ≤ target.depth

/-- Decide whether distinct source provider paths fit one distinct joint
provider path. Only literal key metadata is inspected. -/
def SharedBase.acceptsKeys (target : List BaseContext.ConstantKey)
    (sources : List (List BaseContext.ConstantKey)) : Bool :=
  decide target.Nodup && sources.all (fun source => decide (source.Nodup ∧ source ⊆ target))

/-- The executable metadata check accepts exactly distinct contained paths. -/
theorem SharedBase.acceptsKeys_eq_true_iff (target : List BaseContext.ConstantKey)
    (sources : List (List BaseContext.ConstantKey)) :
    SharedBase.acceptsKeys target sources = true ↔
      target.Nodup ∧ ∀ source ∈ sources, source.Nodup ∧ source ⊆ target := by
  simp only [SharedBase.acceptsKeys, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]

/-- Select the first installed jointly compatible prefix, in catalog order,
and retain every requested infinitesimal predecessor. No provider premises
are manufactured and no positional coefficient map is computed by this search.
Gathering uses the first eligible prefix without trying later entries; semantic
success therefore uses the catalog model invariant. -/
def SharedBase.chooseReconciled? (catalog : BaseContext.Catalog registry)
    (sources : List (BaseContext.PackedContext registry)) : Option (SharedBase.Reconciled sources) :=
  let allowed := fun candidate : BaseContext.RealPrefix registry =>
    SharedBase.acceptsKeys candidate.keys (sources.map (·.signature.constants))
  match selected : catalog.prefixes.find? allowed with
  | none => none
  | some candidate => some ⟨candidate.finish.extend (SharedBase.depth sources), by
      have accepted := List.find?_some (p := allowed) (a := candidate)
        (l := catalog.prefixes) selected
      simp only [allowed, SharedBase.acceptsKeys, List.all_map, Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq] at accepted
      simpa only [BaseContext.PackedContext.extend_signature,
        BaseContext.RealPrefix.finish_signature] using accepted.1,
    by
      have accepted := List.find?_some (p := allowed) (a := candidate)
        (l := catalog.prefixes) selected
      simp only [allowed, SharedBase.acceptsKeys, List.all_map, Function.comp_apply, Bool.and_eq_true, decide_eq_true_eq] at accepted
      intro source member
      have keys := of_decide_eq_true (List.all_eq_true.mp accepted.2 source member)
      simp only [BaseContext.PackedContext.extend_signature,
        BaseContext.RealPrefix.finish_signature, BaseContext.PackedContext.depth, Nat.zero_add]
      exact ⟨keys.1, keys.2, SharedBase.depth_bound sources source member⟩⟩

/-- Selection succeeds exactly when an installed distinct prefix contains all
source provider keys; source order is immaterial. -/
theorem SharedBase.chooseReconciled?_isSome (catalog : BaseContext.Catalog registry)
    (sources : List (BaseContext.PackedContext registry)) :
    (SharedBase.chooseReconciled? catalog sources).isSome = true ↔
      ∃ candidate ∈ catalog.prefixes, candidate.keys.Nodup ∧
        ∀ source ∈ sources, source.signature.constants.Nodup ∧
          source.signature.constants ⊆ candidate.keys := by
  have agrees : (SharedBase.chooseReconciled? catalog sources).isSome =
      (catalog.prefixes.find? (fun candidate => SharedBase.acceptsKeys candidate.keys
        (sources.map (·.signature.constants)))).isSome := by
    unfold chooseReconciled?
    dsimp only
    split <;> simp_all only [Option.isSome_none, Option.isSome_some]
  rw [agrees]
  simp only [List.find?_isSome, SharedBase.acceptsKeys_eq_true_iff, List.mem_map]
  constructor
  · rintro ⟨candidate, installed, distinct, keys⟩
    exact ⟨candidate, installed, distinct, fun source member => keys _ ⟨source, member, rfl⟩⟩
  · rintro ⟨candidate, installed, distinct, keys⟩
    refine ⟨candidate, installed, distinct, ?_⟩
    rintro path ⟨source, member, rfl⟩
    exact keys source member

/-- A jointly validated installed prefix suffices for all distinct source
key paths, including incomparable paths and different provider orders. -/
theorem SharedBase.chooseReconciled?_success (catalog : BaseContext.Catalog registry)
    (sources : List (BaseContext.PackedContext registry)) (candidate : BaseContext.RealPrefix registry)
    (installed : candidate ∈ catalog.prefixes) (distinct : candidate.keys.Nodup)
    (keys : ∀ source ∈ sources, source.signature.constants.Nodup ∧
      source.signature.constants ⊆ candidate.keys) :
    (SharedBase.chooseReconciled? catalog sources).isSome = true :=
  (SharedBase.chooseReconciled?_isSome catalog sources).mpr ⟨candidate, installed, distinct, keys⟩

/-- The chosen target retains the actual installed prefix and the maximum
requested depth, so its provider model can be recovered without guessing. -/
theorem SharedBase.chooseReconciled?_target (catalog : BaseContext.Catalog registry)
    (sources : List (BaseContext.PackedContext registry)) (shared : SharedBase.Reconciled sources)
    (accepted : SharedBase.chooseReconciled? catalog sources = some shared) :
    ∃ candidate ∈ catalog.prefixes,
      shared.target = candidate.finish.extend (SharedBase.depth sources) := by
  unfold SharedBase.chooseReconciled? at accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · rename_i candidate selected
    cases Option.some.inj accepted
    exact ⟨candidate, List.mem_of_find?_eq_some selected, rfl⟩

/-- Select a jointly validated base, then retain all original owner maps and
rebuild the dependency cache through provider reconciliation. -/
@[expose] def Shared.gatherReconciledFrom? (catalog : BaseContext.Catalog registry)
    (owners : List (Context registry)) : Option (Σ base, Shared base owners) := do
  let chosen ← SharedBase.chooseReconciled? catalog (owners.map (·.origin.base))
  let shared ← Shared.gatherReconciled? chosen.target owners
  return ⟨chosen.target, shared⟩

/-- Successful selection and gathering determine the exact returned packet. -/
theorem Shared.gatherReconciledFrom?_of_success (catalog : BaseContext.Catalog registry)
    (owners : List (Context registry)) (chosen : SharedBase.Reconciled (owners.map (·.origin.base)))
    (selected : SharedBase.chooseReconciled? catalog (owners.map (·.origin.base)) = some chosen)
    (shared : Shared chosen.target owners)
    (gathered : Shared.gatherReconciled? chosen.target owners = some shared) :
    Shared.gatherReconciledFrom? catalog owners = some ⟨chosen.target, shared⟩ := by
  simp only [Shared.gatherReconciledFrom?, selected, gathered, bind, Option.bind, pure]

/-- The automatic factory returns the underlying reconciled gather unchanged. -/
theorem Shared.gatherReconciledFrom?_gathered (catalog : BaseContext.Catalog registry)
    (owners : List (Context registry)) (base : BaseContext.PackedContext registry)
    (shared : Shared base owners)
    (accepted : Shared.gatherReconciledFrom? catalog owners = some ⟨base, shared⟩) :
    Shared.gatherReconciled? base owners = some shared := by
  unfold Shared.gatherReconciledFrom? at accepted
  cases selected : SharedBase.chooseReconciled? catalog (owners.map (·.origin.base)) with
  | none => simp [selected, bind, Option.bind] at accepted
  | some chosen =>
    simp only [selected, bind, Option.bind] at accepted
    cases gathered : Shared.gatherReconciled? chosen.target owners with
    | none => simp [gathered, bind, Option.bind] at accepted
    | some result =>
      simp only [gathered, bind, Option.bind, pure] at accepted
      cases Option.some.inj accepted
      exact gathered

/-- Recover the installed prefix behind an automatically reconciled target. -/
theorem Shared.gatherReconciledFrom?_base (catalog : BaseContext.Catalog registry)
    (owners : List (Context registry)) (base : BaseContext.PackedContext registry)
    (shared : Shared base owners)
    (accepted : Shared.gatherReconciledFrom? catalog owners = some ⟨base, shared⟩) :
    ∃ candidate ∈ catalog.prefixes,
      base = candidate.finish.extend (SharedBase.depth (owners.map (·.origin.base))) := by
  unfold Shared.gatherReconciledFrom? at accepted
  cases selected : SharedBase.chooseReconciled? catalog (owners.map (·.origin.base)) with
  | none => simp [selected, bind, Option.bind] at accepted
  | some chosen =>
    simp only [selected, bind, Option.bind] at accepted
    cases gathered : Shared.gatherReconciled? chosen.target owners with
    | none => simp [gathered, bind, Option.bind] at accepted
    | some result =>
      simp only [gathered, bind, Option.bind, pure] at accepted
      cases Option.some.inj accepted
      exact SharedBase.chooseReconciled?_target catalog _ chosen selected

/-- Select a common installed prefix and transport the complete original
request, including all root predecessors, through checked reconciled maps. -/
@[expose] def Live.Request.gatherReconciledFrom? (catalog : BaseContext.Catalog registry)
    (request : Live.Request registry) : Option (Σ base, Live.Collection base request) := do
  let chosen ← SharedBase.chooseReconciled? catalog (request.owners.map (·.origin.base))
  let collection ← request.gatherReconciled? chosen.target
  return ⟨chosen.target, collection⟩

/-- The catalog factory retains the underlying complete live collection. -/
theorem Live.Request.gatherReconciledFrom?_of_success (catalog : BaseContext.Catalog registry)
    (request : Live.Request registry)
    (chosen : SharedBase.Reconciled (request.owners.map (·.origin.base)))
    (selected : SharedBase.chooseReconciled? catalog (request.owners.map (·.origin.base)) = some chosen)
    (collection : Live.Collection chosen.target request)
    (gathered : request.gatherReconciled? chosen.target = some collection) :
    request.gatherReconciledFrom? catalog = some ⟨chosen.target, collection⟩ := by
  simp only [Live.Request.gatherReconciledFrom?, selected, gathered, bind, Option.bind, pure]

/-- Every returned collection was accepted by the actual reconciled live factory. -/
theorem Live.Request.gatherReconciledFrom?_gathered (catalog : BaseContext.Catalog registry)
    (request : Live.Request registry) (base : BaseContext.PackedContext registry)
    (collection : Live.Collection base request)
    (accepted : request.gatherReconciledFrom? catalog = some ⟨base, collection⟩) :
    request.gatherReconciled? base = some collection := by
  unfold Live.Request.gatherReconciledFrom? at accepted
  cases selected : SharedBase.chooseReconciled? catalog (request.owners.map (·.origin.base)) with
  | none => simp [selected, bind, Option.bind] at accepted
  | some chosen =>
    simp only [selected, bind, Option.bind] at accepted
    cases gathered : request.gatherReconciled? chosen.target with
    | none => simp [gathered, bind, Option.bind] at accepted
    | some result =>
      simp only [gathered, bind, Option.bind, pure] at accepted
      cases Option.some.inj accepted
      exact gathered

/-- Retrieve the exact installed prefix and automatically selected depth. -/
theorem Live.Request.gatherReconciledFrom?_base (catalog : BaseContext.Catalog registry)
    (request : Live.Request registry) (base : BaseContext.PackedContext registry)
    (collection : Live.Collection base request)
    (accepted : request.gatherReconciledFrom? catalog = some ⟨base, collection⟩) :
    ∃ candidate ∈ catalog.prefixes,
      base = candidate.finish.extend (SharedBase.depth (request.owners.map (·.origin.base))) := by
  unfold Live.Request.gatherReconciledFrom? at accepted
  cases selected : SharedBase.chooseReconciled? catalog (request.owners.map (·.origin.base)) with
  | none => simp [selected, bind, Option.bind] at accepted
  | some chosen =>
    simp only [selected, bind, Option.bind] at accepted
    cases gathered : request.gatherReconciled? chosen.target with
    | none => simp [gathered, bind, Option.bind] at accepted
    | some result =>
      simp only [gathered, bind, Option.bind, pure] at accepted
      cases Option.some.inj accepted
      exact SharedBase.chooseReconciled?_target catalog _ chosen selected

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.SharedBase.chooseReconciled?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.SharedBase.chooseReconciled?_isSome

/-- info: 'Hex.RealClosure.Tower.SharedBase.chooseReconciled?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.SharedBase.chooseReconciled?_success

/-- info: 'Hex.RealClosure.Tower.SharedBase.chooseReconciled?_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.SharedBase.chooseReconciled?_target



/-- info: 'Hex.RealClosure.Tower.Shared.gatherReconciledFrom?_gathered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.gatherReconciledFrom?_gathered

/-- info: 'Hex.RealClosure.Tower.Shared.gatherReconciledFrom?_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.gatherReconciledFrom?_base

/-- info: 'Hex.RealClosure.Tower.Live.Request.gatherReconciledFrom?_gathered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Request.gatherReconciledFrom?_gathered

/-- info: 'Hex.RealClosure.Tower.Live.Request.gatherReconciledFrom?_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Request.gatherReconciledFrom?_base

/-- info: 'Hex.RealClosure.Tower.SharedBase.acceptsKeys_eq_true_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.SharedBase.acceptsKeys_eq_true_iff
