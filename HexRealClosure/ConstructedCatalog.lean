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

/-- A newly constructed native provider history and its exact catalog insertion.
Existing entries are preserved by the ordinary immutable insertion operation. -/
structure Catalog.Construction {registry : Registry} (catalog : Catalog registry)
    (read : (parent : RealPrefix registry) → (key : ConstantKey) → Option (parent.Step key))
    (parent : RealPrefix registry) (keys : List ConstantKey) : Type 1 where
  private mk ::
  target : RealPrefix registry
  next : Catalog registry
  built : RealPrefix.extend? read parent keys = some target
  inserted : catalog.insert target = some next

/-- Build a missing target history before installing it. Missing relative
progress or an already installed complete path rejects. The catalog never
substitutes an existing target for a failed construction. -/
def Catalog.construct? {registry : Registry} (catalog : Catalog registry)
    (read : (parent : RealPrefix registry) → (key : ConstantKey) → Option (parent.Step key))
    (parent : RealPrefix registry) (keys : List ConstantKey) :
    Option (catalog.Construction read parent keys) :=
  match built : RealPrefix.extend? read parent keys with
  | none => none
  | some target =>
    match inserted : catalog.insert target with
    | none => none
    | some next => some ⟨target, next, built, inserted⟩

/-- Installation succeeds whenever the native construction succeeds and its
complete output path is absent from the current catalog. No target is supplied. -/
theorem Catalog.construct?_success {registry : Registry} (catalog : Catalog registry)
    (read : (parent : RealPrefix registry) → (key : ConstantKey) → Option (parent.Step key))
    (parent : RealPrefix registry) (keys : List ConstantKey)
    (ready : (RealPrefix.extend? read parent keys).isSome = true)
    (missing : ∀ target, RealPrefix.extend? read parent keys = some target →
      catalog.lookup target.keys = none) :
    (catalog.construct? read parent keys).isSome = true := by
  unfold Catalog.construct?
  split
  · rename_i built
    simp only [built, Option.isSome_none, Bool.false_eq_true] at ready
  · rename_i target built
    have inserts := (Catalog.insert_isSome_iff catalog target).mpr (missing target built)
    split
    · rename_i inserted
      simp only [inserted, Option.isSome_none, Bool.false_eq_true] at inserts
    · rfl

/-- The actual installed target is available for the ordinary gather factory. -/
theorem Catalog.Construction.installed {registry : Registry} {catalog : Catalog registry}
    {read : (parent : RealPrefix registry) → (key : ConstantKey) → Option (parent.Step key)}
    {parent : RealPrefix registry} {keys : List ConstantKey}
    (packet : catalog.Construction read parent keys) : packet.target ∈ packet.next.prefixes :=
  (Catalog.mem_prefixes_of_insert catalog packet.next packet.target packet.target
    packet.inserted).mpr (Or.inl rfl)

/-- Every old catalog entry remains valid in the newly returned catalog. -/
theorem Catalog.Construction.preserved {registry : Registry} {catalog : Catalog registry}
    {read : (parent : RealPrefix registry) → (key : ConstantKey) → Option (parent.Step key)}
    {parent : RealPrefix registry} {keys : List ConstantKey}
    (packet : catalog.Construction read parent keys) (candidate : RealPrefix registry)
    (old : candidate ∈ catalog.prefixes) : candidate ∈ packet.next.prefixes :=
  (Catalog.mem_prefixes_of_insert catalog packet.next packet.target candidate
    packet.inserted).mpr (Or.inr old)

/-- All original and requested keys occur in the same newly installed history. -/
theorem Catalog.Construction.covers {registry : Registry} {catalog : Catalog registry}
    {read : (parent : RealPrefix registry) → (key : ConstantKey) → Option (parent.Step key)}
    {parent : RealPrefix registry} {keys : List ConstantKey}
    (packet : catalog.Construction read parent keys) (key : ConstantKey)
    (requested : key ∈ parent.keys ∨ key ∈ keys) : key ∈ packet.target.keys :=
  (RealPrefix.extend?_mem read parent keys packet.built key).mpr requested

end Hex.RealClosure.BaseContext
