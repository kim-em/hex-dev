/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BaseHistory
public import HexRealClosure.BaseCatalog

public section
namespace Hex.RealClosure.BaseContext

/-- A constructed native provider history and its retained catalog.
Existing entries are preserved; an already installed path is reused. -/
structure Catalog.Construction {registry : Registry} (catalog : Catalog registry)
    (read : (parent : RealPrefix registry) → (key : ConstantKey) → Option (parent.Step key))
    (parent : RealPrefix registry) (keys : List ConstantKey) : Type 1 where
  private mk ::
  target : RealPrefix registry
  next : Catalog registry
  built : RealPrefix.extend? read parent keys = some target
  inserted : next = catalog ∨ catalog.insert target = some next
  available : next.lookup target.keys = some target

/-- Build the target history, then install it or reuse its existing catalog
entry. Missing relative progress rejects. The catalog never substitutes an
existing target for a failed construction. -/
def Catalog.construct? {registry : Registry} (catalog : Catalog registry)
    (read : (parent : RealPrefix registry) → (key : ConstantKey) → Option (parent.Step key))
    (parent : RealPrefix registry) (keys : List ConstantKey) :
    Option (catalog.Construction read parent keys) :=
  match built : RealPrefix.extend? read parent keys with
  | none => none
  | some target =>
    match found : catalog.lookup target.keys with
    | some existing =>
      have same : existing = target := RealPrefix.keys_inj
        (catalog.lookup_keys target.keys existing found)
      some ⟨target, catalog, built, Or.inl rfl, same ▸ found⟩
    | none =>
      match inserted : catalog.insert target with
      | none => none
      | some next => some ⟨target, next, built, Or.inr inserted, by
          have lookup := catalog.lookup_insert target found
          simpa only [inserted, Option.bind_some] using lookup⟩

/-- Installation or reuse succeeds whenever the native construction succeeds.
No target prefix or absence condition is supplied. -/
theorem Catalog.construct?_success {registry : Registry} (catalog : Catalog registry)
    (read : (parent : RealPrefix registry) → (key : ConstantKey) → Option (parent.Step key))
    (parent : RealPrefix registry) (keys : List ConstantKey)
    (ready : (RealPrefix.extend? read parent keys).isSome = true) :
    (catalog.construct? read parent keys).isSome = true := by
  unfold Catalog.construct?
  split
  · rename_i built
    simp only [built, Option.isSome_none, Bool.false_eq_true] at ready
  · rename_i target built
    split
    · rfl
    · rename_i missing
      have inserts := (Catalog.insert_isSome_iff catalog target).mpr missing
      split
      · rename_i inserted
        simp only [inserted, Option.isSome_none, Bool.false_eq_true] at inserts
      · rfl

/-- Reusing an installed complete output returns the original catalog. -/
theorem Catalog.construct?_reuse {registry : Registry} (catalog : Catalog registry)
    (read : (parent : RealPrefix registry) → (key : ConstantKey) → Option (parent.Step key))
    (parent : RealPrefix registry) (keys : List ConstantKey) (target : RealPrefix registry)
    (built : RealPrefix.extend? read parent keys = some target)
    (found : catalog.lookup target.keys = some target) :
    ∃ packet : catalog.Construction read parent keys,
      catalog.construct? read parent keys = some packet ∧ packet.next = catalog ∧
        packet.target = target := by
  unfold Catalog.construct?
  split
  · rename_i missing
    rw [built] at missing
    cases missing
  · rename_i actual accepted
    have same : actual = target := Option.some.inj (accepted.symm.trans built)
    subst actual
    split
    · exact ⟨_, rfl, rfl, rfl⟩
    · rename_i missing
      rw [found] at missing
      cases missing

/-- A failed native extension cannot change the catalog or select an existing
history in place of the missing provider progress. -/
theorem Catalog.construct?_missing {registry : Registry} (catalog : Catalog registry)
    (read : (parent : RealPrefix registry) → (key : ConstantKey) → Option (parent.Step key))
    (parent : RealPrefix registry) (keys : List ConstantKey)
    (missing : RealPrefix.extend? read parent keys = none) :
    catalog.construct? read parent keys = none := by
  unfold Catalog.construct?
  split
  · rfl
  · rename_i target accepted
    rw [missing] at accepted
    cases accepted

/-- The actual constructed target is available for gathering and later reads. -/
theorem Catalog.Construction.installed {registry : Registry} {catalog : Catalog registry}
    {read : (parent : RealPrefix registry) → (key : ConstantKey) → Option (parent.Step key)}
    {parent : RealPrefix registry} {keys : List ConstantKey}
    (packet : catalog.Construction read parent keys) : packet.target ∈ packet.next.prefixes :=
  packet.next.lookup_mem packet.target.keys packet.target packet.available

/-- Every old catalog entry remains valid in the returned catalog. -/
theorem Catalog.Construction.preserved {registry : Registry} {catalog : Catalog registry}
    {read : (parent : RealPrefix registry) → (key : ConstantKey) → Option (parent.Step key)}
    {parent : RealPrefix registry} {keys : List ConstantKey}
    (packet : catalog.Construction read parent keys) (candidate : RealPrefix registry)
    (old : candidate ∈ catalog.prefixes) : candidate ∈ packet.next.prefixes := by
  rcases packet.inserted with unchanged | inserted
  · simpa only [unchanged] using old
  · exact (Catalog.mem_prefixes_of_insert catalog packet.next packet.target candidate
      inserted).mpr (Or.inr old)

/-- All original and requested keys occur in the same newly installed history. -/
theorem Catalog.Construction.covers {registry : Registry} {catalog : Catalog registry}
    {read : (parent : RealPrefix registry) → (key : ConstantKey) → Option (parent.Step key)}
    {parent : RealPrefix registry} {keys : List ConstantKey}
    (packet : catalog.Construction read parent keys) (key : ConstantKey)
    (requested : key ∈ parent.keys ∨ key ∈ keys) : key ∈ packet.target.keys :=
  (RealPrefix.extend?_mem read parent keys packet.built key).mpr requested

end Hex.RealClosure.BaseContext
