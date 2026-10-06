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

end Hex.RealClosure.Tower
