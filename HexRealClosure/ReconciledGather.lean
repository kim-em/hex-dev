/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.LiveContext
public import HexRealClosure.TowerInclusion
import all HexRealClosure.LiveContext
import all HexRealClosure.BaseReconciliation

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry}

/-- The nominal factory retains exactly the success of its native map reader. -/
theorem BaseReconciliation.make?_isSome (source target : BaseContext.PackedContext registry) :
    (BaseReconciliation.make? source target).isSome = (source.reconcile? target).isSome := by
  unfold BaseReconciliation.make?
  split <;> simp_all only [Option.isSome_none, Option.isSome_some]

/-- Register an actual owner after checking provider-key reconciliation once.
Suffix rebuilding and all cache reuse use that retained native inclusion. -/
def Shared.registerReconciledOrigin? {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    {source : Context registry} (origin : Origin source) : Option (Registration shared source) := do
  let previous ← Inclusion.reconcileBase? origin.base base
  shared.registerBase? origin previous

/-- Register a live context with provider reordering and retain the actual
old-target and new-owner inclusions. -/
def Shared.registerReconciled? {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (source : Context registry) : Option (Registration shared source) :=
  shared.registerReconciledOrigin? source.origin

/-- Add one original owner through checked provider reordering. -/
def Shared.addReconciled? {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (source : Context registry) : Option (Shared base (owners ++ [source])) :=
  (shared.registerReconciled? source).map Registration.shared

/-- Gather owners in their retained order, composing every old map with the
same target inclusion whenever rebuilding adds an algebraic dependency. -/
def Shared.collectReconciled? {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners) :
    (later : List (Context registry)) → Option (Shared base (owners ++ later))
  | [] => some (_root_.cast (congrArg (Shared base) (List.append_nil owners).symm) shared)
  | source :: rest => do
    let added ← shared.addReconciled? source
    let result ← added.collectReconciled? rest
    return _root_.cast (congrArg (Shared base) (List.append_assoc owners [source] rest)) result

/-- Gather original contexts in a supplied compatible actual base, accepting
provider permutations and retaining their dependency-closed checked inclusions. -/
def Shared.gatherReconciled? (base : BaseContext.PackedContext registry)
    (owners : List (Context registry)) : Option (Shared base owners) :=
  (Shared.empty base).collectReconciled? owners

/-- At an accepted ordered base inclusion, reconciled registration returns the
identical existing packet, including caches and every retained map. -/
theorem Shared.registerReconciledOrigin?_ordered {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    {source : Context registry} (origin : Origin source)
    (previous : Inclusion (Context.ofBase origin.base) (Context.ofBase base))
    (produced : Inclusion.base? origin.base base = some previous) :
    shared.registerReconciledOrigin? origin = shared.registerOrigin? origin := by
  unfold Shared.registerReconciledOrigin?
  rw [Inclusion.reconcileBase?_ordered previous produced]
  simp only [Shared.registerOrigin?, produced, bind, Option.bind]

/-- An accepted registration has already checked the provider-key inclusion
and infinitesimal depth. A realized target supplies its key distinctness. -/
theorem Shared.registerReconciledOrigin?_compatible
    {base : BaseContext.PackedContext registry} {owners : List (Context registry)}
    (shared : Shared base owners) {source : Context registry} (origin : Origin source)
    (targetUnique : base.signature.constants.Nodup) (packet : Registration shared source)
    (produced : shared.registerReconciledOrigin? origin = some packet) :
    origin.base.signature.constants.Nodup ∧
      origin.base.signature.constants ⊆ base.signature.constants ∧
      origin.base.signature.infinitesimals ≤ base.signature.infinitesimals := by
  have accepted : (Inclusion.reconcileBase? origin.base base).isSome = true := by
    cases checked : Inclusion.reconcileBase? origin.base base with
    | none =>
      simp only [Shared.registerReconciledOrigin?, checked, bind, Option.bind] at produced
      contradiction
    | some inclusion => rfl
  rw [Inclusion.reconcileBase?_eq, Option.isSome_map, BaseReconciliation.make?_isSome] at accepted
  exact BaseContext.PackedContext.reconcile?_conditions _ _ targetUnique accepted

/-- A successful addition certifies the original owner's compatibility. -/
theorem Shared.addReconciled?_compatible {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (targetUnique : base.signature.constants.Nodup)
    (source : Context registry) (result : Shared base (owners ++ [source]))
    (produced : shared.addReconciled? source = some result) :
    source.origin.base.signature.constants.Nodup ∧
      source.origin.base.signature.constants ⊆ base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals := by
  cases checked : shared.registerReconciled? source with
  | none =>
    simp only [Shared.addReconciled?, checked, Option.map_none] at produced
    contradiction
  | some packet =>
    exact shared.registerReconciledOrigin?_compatible source.origin targetUnique packet checked

/-- Every owner in an accepted collection satisfies the factory's actual
provider and depth checks, including owners reused from the cache. -/
theorem Shared.collectReconciled?_compatible {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (targetUnique : base.signature.constants.Nodup) (later : List (Context registry))
    (result : Shared base (owners ++ later))
    (produced : shared.collectReconciled? later = some result) :
    ∀ source ∈ later,
      source.origin.base.signature.constants.Nodup ∧
      source.origin.base.signature.constants ⊆ base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals := by
  induction later generalizing owners with
  | nil => simp
  | cons source rest ih =>
    simp only [Shared.collectReconciled?] at produced
    cases first : shared.addReconciled? source with
    | none => simp only [first, bind, Option.bind] at produced; contradiction
    | some added =>
      cases following : added.collectReconciled? rest with
      | none => simp only [first, following, bind, Option.bind] at produced; contradiction
      | some collected =>
        intro owner present
        rcases List.mem_cons.mp present with equal | present
        · subst owner
          exact shared.addReconciled?_compatible targetUnique source added first
        · exact ih added collected following owner present

/-- The accepted gather result supplies all source compatibility premises. -/
theorem Shared.gatherReconciled?_compatible (base : BaseContext.PackedContext registry)
    (targetUnique : base.signature.constants.Nodup) (owners : List (Context registry))
    (shared : Shared base owners)
    (produced : Shared.gatherReconciled? base owners = some shared) :
    ∀ source ∈ owners,
      source.origin.base.signature.constants.Nodup ∧
      source.origin.base.signature.constants ⊆ base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals := by
  exact (Shared.empty base).collectReconciled?_compatible targetUnique owners shared produced

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.BaseReconciliation.make?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseReconciliation.make?_isSome

/-- info: 'Hex.RealClosure.Tower.Shared.registerReconciledOrigin?_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.registerReconciledOrigin?_ordered

/-- info: 'Hex.RealClosure.Tower.Shared.gatherReconciled?_compatible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.gatherReconciled?_compatible
