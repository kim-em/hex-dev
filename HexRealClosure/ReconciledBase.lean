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

/-- Select the first installed jointly compatible prefix, in catalog order,
and retain every requested infinitesimal predecessor. No provider premises
are manufactured and no positional coefficient map is computed by this search. -/
def SharedBase.chooseReconciled? (catalog : BaseContext.Catalog registry)
    (sources : List (BaseContext.PackedContext registry)) : Option (SharedBase.Reconciled sources) :=
  let allowed := fun candidate : BaseContext.RealPrefix registry =>
    decide candidate.keys.Nodup && sources.all (fun source =>
      decide (source.signature.constants.Nodup ∧ source.signature.constants ⊆ candidate.keys))
  match selected : catalog.prefixes.find? allowed with
  | none => none
  | some candidate => some ⟨candidate.finish.extend (SharedBase.depth sources), by
      have accepted := List.find?_some (p := allowed) (a := candidate)
        (l := catalog.prefixes) selected
      simp only [allowed, Bool.and_eq_true, decide_eq_true_eq] at accepted
      simpa only [BaseContext.PackedContext.extend_signature,
        BaseContext.RealPrefix.finish_signature] using accepted.1,
    by
      have accepted := List.find?_some (p := allowed) (a := candidate)
        (l := catalog.prefixes) selected
      simp only [allowed, Bool.and_eq_true, decide_eq_true_eq] at accepted
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
      (catalog.prefixes.find? (fun candidate => decide candidate.keys.Nodup &&
        sources.all (fun source => decide (source.signature.constants.Nodup ∧
          source.signature.constants ⊆ candidate.keys)))).isSome := by
    unfold chooseReconciled?
    dsimp only
    split <;> simp_all only [Option.isSome_none, Option.isSome_some]
  rw [agrees]
  simp only [List.find?_isSome, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]

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

/-- Every selected source has an actual native checked inclusion into the
chosen target. Reading it computes that source's coefficient map once. -/
def SharedBase.Reconciled.inclusion {sources : List (BaseContext.PackedContext registry)}
    (shared : SharedBase.Reconciled sources) (source : BaseContext.PackedContext registry)
    (member : source ∈ sources) : Inclusion (Context.ofBase source) (Context.ofBase shared.target) :=
  (Inclusion.reconcileBase? source shared.target).get (by
    rw [Inclusion.reconcileBase?_eq, Option.isSome_map, BaseReconciliation.make?_isSome]
    have compatible := shared.included source member
    exact BaseContext.PackedContext.reconcile?_success source shared.target
      compatible.1 shared.distinct compatible.2.1 compatible.2.2)

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

/-- info: 'Hex.RealClosure.Tower.SharedBase.Reconciled.inclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.SharedBase.Reconciled.inclusion

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
