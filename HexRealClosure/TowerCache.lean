/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerIdentity
public import HexRealClosure.TowerInclusion
public import HexRealClosure.TowerEnlarge

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry}

/-- Original predecessor contexts and their checked inclusions in one target.
Entries retain native owners; neither a name nor a hash supplies an equality. -/
structure InclusionCache (target : Context registry) : Type 1 where
  entries : List (Σ source : Context registry, Inclusion source target)

/-- Carry all cached original predecessors through the same target inclusion. -/
@[expose] def InclusionCache.extend {source target : Context registry}
    (cache : InclusionCache source) (next : Inclusion source target) : InclusionCache target :=
  ⟨cache.entries.map fun entry => ⟨entry.1, entry.2.comp next⟩⟩

/-- Retain a checked map for an actual original predecessor. -/
@[expose] def InclusionCache.insert {source target : Context registry}
    (cache : InclusionCache target) (next : Inclusion source target) : InclusionCache target :=
  ⟨⟨source, next⟩ :: cache.entries⟩

/-- Retain two collections of checked predecessors in the same target. -/
@[expose] def InclusionCache.append {target : Context registry}
    (first second : InclusionCache target) : InclusionCache target :=
  ⟨first.entries ++ second.entries⟩

/-- Checked inclusions of an actual suffix's native predecessors. -/
structure Suffix.Prefixes {source : Context registry} (suffix : Suffix source) : Type 1 where
  inclusion : Inclusion source suffix.context
  cache : InclusionCache suffix.context

/-- Retain every native predecessor of a suffix, including its final target.
All maps use the actual coefficient inclusions of its stored descriptors. -/
def Suffix.prefixes {source : Context registry} (suffix : Suffix source) : suffix.Prefixes :=
  match suffix with
  | .nil =>
    let inclusion := Inclusion.identity source
    ⟨inclusion, (InclusionCache.mk []).insert inclusion⟩
  | .root descriptor rest =>
    let child := source.adjoin descriptor
    let first : Inclusion source child.context :=
      ⟨Conversion.includeRoot source descriptor child rfl,
        (Conversion.includeRoot_spec source descriptor child rfl).1⟩
    let later := rest.prefixes
    let inclusion := first.comp later.inclusion
    ⟨inclusion, later.cache.insert inclusion⟩

private def findInclusion {target : Context registry} (source : Context registry) :
    List (Σ owner : Context registry, Inclusion owner target) → Option (Inclusion source target)
  | [] => none
  | ⟨owner, inclusion⟩ :: rest =>
    if same : source = owner then some (same.symm ▸ inclusion)
    else findInclusion source rest

/-- Look up a predecessor by checked native context equality. -/
def InclusionCache.find? {target : Context registry}
    (cache : InclusionCache target) (source : Context registry) : Option (Inclusion source target) :=
  findInclusion source cache.entries

/-- Inserting an owner makes its exact checked inclusion available. -/
theorem InclusionCache.find?_insert {source target : Context registry}
    (cache : InclusionCache target) (next : Inclusion source target) :
    (cache.insert next).find? source = some next := by
  simp [InclusionCache.find?, InclusionCache.insert, findInclusion]

/-- One shared extension, retaining the original owner and every predecessor. -/
structure CacheResult (previous original : Context registry) : Type 1 where
  target : Context registry
  inclusion : Inclusion previous target
  original : Inclusion original target
  cache : InclusionCache target
  base_eq : target.origin.base = previous.origin.base

/-- Traverse original dependencies in order, reusing their cached inclusions.
Only a previously unseen exact predecessor is adjoined to the shared target. -/
def InclusionCache.rebuild? {target source : Context registry}
    (cache : InclusionCache target) (initial : Inclusion source target)
    (suffix : Suffix source) : Option (CacheResult target suffix.context) :=
  match suffix with
  | .nil => some ⟨target, Inclusion.identity target, initial, cache, rfl⟩
  | .root descriptor rest =>
    let original := (source.adjoin descriptor).context
    match cache.find? original with
    | some found => cache.rebuild? found rest
    | none =>
      match checked : SignDet.Descriptor.validate target.sign target.signature
          (source.mapDescriptor target initial.value descriptor) with
      | none => none
      | some converted =>
        let child := target.adjoin converted
        let previous : Inclusion target child.context :=
          ⟨Conversion.includeRoot target converted child rfl,
            (Conversion.includeRoot_spec target converted child rfl).1⟩
        let next : Inclusion original child.context :=
          ⟨initial.native.adjoinCached descriptor converted checked child rfl,
            (initial.native.adjoinCached_spec descriptor converted checked child rfl).1⟩
        let updated := ((cache.extend previous).insert next).insert
          (Inclusion.identity child.context)
        match updated.rebuild? next rest with
        | none => none
        | some later =>
          some ⟨later.target, previous.comp later.inclusion, later.original, later.cache,
            later.base_eq.trans (by
              rw [Context.origin_adjoin, Origin.snoc_base])⟩

/-- An exactly registered predecessor is reused in the same target, with its exact
cached map and without adding another algebraic level. -/
theorem InclusionCache.rebuild?_cached {target source : Context registry}
    (cache : InclusionCache target) (initial : Inclusion source target)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (found : Inclusion (source.adjoin descriptor).context target)
    (present : cache.find? (source.adjoin descriptor).context = some found) :
    cache.rebuild? initial (.root descriptor .nil) =
      some ⟨target, Inclusion.identity target, found, cache, rfl⟩ := by
  simp only [InclusionCache.rebuild?, present]
  rfl

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.InclusionCache.find?_insert' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.InclusionCache.find?_insert

/-- info: 'Hex.RealClosure.Tower.InclusionCache.rebuild?_cached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.InclusionCache.rebuild?_cached
