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

/-- Rebuild an original owner's suffix from one already checked base inclusion.
The result retains the old target map, all owner maps and the updated cache. -/
def Shared.registerBase? {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    {source : Context registry} (origin : Origin source)
    (previous : Inclusion (Context.ofBase origin.base) (Context.ofBase base)) :
    Option (Registration shared source) := by
  cases origin with
  | pack original suffix source_eq =>
    exact do
      let starting := previous.comp (Inclusion.mk shared.input rfl)
      let rebuilt ← shared.cache.rebuild? starting suffix
      let combined := ((Inclusion.mk shared.input rfl).comp rebuilt.inclusion).native
      let newest : Inclusion source rebuilt.target := source_eq ▸ rebuilt.original
      let result : Shared base (owners ++ [source]) :=
        ⟨combined, (shared.maps.extend rebuilt.inclusion).snoc newest,
          rebuilt.base_eq.trans shared.base_eq, rebuilt.cache⟩
      return ⟨result, rebuilt.inclusion, newest, rfl⟩

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

/-- A successful cached rebuild returns the exact registration packet's
conversion, predecessor map, owner family and cache. -/
theorem Shared.registerBase?_spec {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (original : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base original)) {source : Context registry}
    (same : suffix.context = source)
    (previous : Inclusion (Context.base original) (Context.ofBase base))
    (rebuilt : CacheResult shared.input.context suffix.context)
    (produced : shared.cache.rebuild?
      (previous.comp (Inclusion.mk shared.input rfl)) suffix = some rebuilt) :
    ∃ packet : Registration shared source,
      shared.registerBase? (.pack original suffix same) previous = some packet ∧
      packet.shared.input = ((Inclusion.mk shared.input rfl).comp rebuilt.inclusion).native ∧
      HEq packet.previous rebuilt.inclusion ∧
      HEq packet.shared.maps ((shared.maps.extend rebuilt.inclusion).snoc (_root_.cast
        (congrArg (fun context => Inclusion context rebuilt.target) same) rebuilt.original)) ∧
      HEq packet.shared.cache rebuilt.cache := by
  cases same
  refine ⟨⟨⟨((Inclusion.mk shared.input rfl).comp rebuilt.inclusion).native,
    (shared.maps.extend rebuilt.inclusion).snoc rebuilt.original,
    rebuilt.base_eq.trans shared.base_eq, rebuilt.cache⟩,
    rebuilt.inclusion, rebuilt.original, rfl⟩, ?_, rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
  simp only [Shared.registerBase?, bind, Option.bind, pure]
  rw (config := { transparency := .all }) [produced]

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
  cases origin with
  | pack original suffix same =>
    cases same
    change Inclusion.base? (.pack original) base = some previous at produced
    simp only [Shared.registerBase?, Shared.registerOrigin?, produced, bind, Option.bind, pure]
    rfl

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

/-- info: 'Hex.RealClosure.Tower.Shared.registerBase?_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.registerBase?_spec

/-- info: 'Hex.RealClosure.Tower.Shared.registerReconciledOrigin?_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.registerReconciledOrigin?_ordered

/-- info: 'Hex.RealClosure.Tower.Shared.gatherReconciled?_compatible' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.gatherReconciled?_compatible
