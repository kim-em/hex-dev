/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerIdentity
public import HexRealClosure.TowerInclusion
public import HexRealClosure.TowerEnlarge
public import HexRealClosure.TowerReuse

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry}

/-- Original predecessor contexts and their checked inclusions in one target.
Entries retain native owners; neither a name nor a hash supplies an equality. -/
structure InclusionCache (target : Context registry) : Type 1 where
  entries : List (Σ source : Context registry, Inclusion source target)
  candidates : List target.Value := []

private def findCachedRoot {target : Context registry}
    {descriptor : SignDet.Descriptor target.Value Signature target.sign target.signature}
    (constraints : RootConstraints target descriptor) (seen : List target.Value) :
    List target.Value → Option (RootMatch target descriptor)
  | [] => none
  | candidate :: rest =>
      if seen.contains candidate then findCachedRoot constraints seen rest
      else
        match constraints.match? candidate with
        | some matched => some matched
        | none =>
          let negative := -candidate
          if seen.contains negative || negative == candidate then
            findCachedRoot constraints (candidate :: seen) rest
          else
            match constraints.match? negative with
            | some matched => some matched
            | none => findCachedRoot constraints (negative :: candidate :: seen) rest

/-- Search cached generators and their negatives on demand. A linear head
supplies a coefficient-field candidate first. Every accepted value passes
all selected-root constraints; later entries are untouched after a match. -/
def InclusionCache.findRoot? {target : Context registry}
    (cache : InclusionCache target)
    (descriptor : SignDet.Descriptor target.Value Signature target.sign target.signature) :
    Option (RootMatch target descriptor) :=
  let constraints := RootConstraints.prepare target descriptor
  if descriptor.raw.head.degree? == some 1 then
    let candidate := -descriptor.raw.head.coeff 0 / descriptor.raw.head.coeff 1
    match constraints.match? candidate with
    | some matched => some matched
    | none => findCachedRoot constraints [candidate] cache.candidates
  else findCachedRoot constraints [] cache.candidates

/-- Reuse a checked existing value as the source child's selected generator. -/
@[expose] def Inclusion.reuseRoot {source target : Context registry}
    (initial : Inclusion source target)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (converted : SignDet.Descriptor target.Value Signature target.sign target.signature)
    (binding : converted.raw = source.mapDescriptor target initial.value descriptor)
    (matched : RootMatch target converted) : Inclusion (source.adjoin descriptor).context target :=
  ⟨initial.native.reuseRoot descriptor converted binding matched.value matched.selected,
    initial.native.reuseRoot_context descriptor converted binding matched.value matched.selected⟩

/-- Carry all cached original predecessors through the same target inclusion. -/
@[expose] def InclusionCache.extend {source target : Context registry}
    (cache : InclusionCache source) (next : Inclusion source target) : InclusionCache target :=
  ⟨cache.entries.map fun entry => ⟨entry.1, entry.2.comp next⟩,
    cache.candidates.map next.value⟩

/-- Retain a checked map for an actual original predecessor. -/
@[expose] def InclusionCache.insert {source target : Context registry}
    (cache : InclusionCache target) (next : Inclusion source target) : InclusionCache target :=
  let candidates := match source.lastRoot? with
    | none => cache.candidates
    | some root =>
      let candidate := next.value root
      if cache.candidates.contains candidate then cache.candidates else candidate :: cache.candidates
  ⟨⟨source, next⟩ :: cache.entries, candidates⟩

/-- Retain two collections of checked predecessors in the same target. -/
@[expose] def InclusionCache.append {target : Context registry}
    (first second : InclusionCache target) : InclusionCache target :=
  ⟨first.entries ++ second.entries, (first.candidates ++ second.candidates).eraseDups⟩

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
    ⟨inclusion, (InclusionCache.mk [] []).insert inclusion⟩
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

private theorem findInclusion_mem {target source : Context registry}
    (entries : List (Σ owner : Context registry, Inclusion owner target))
    (found : Inclusion source target)
    (produced : findInclusion source entries = some found) :
    (⟨source, found⟩ : Σ owner : Context registry, Inclusion owner target) ∈ entries := by
  induction entries with
  | nil => simp [findInclusion] at produced
  | cons entry rest ih =>
    rcases entry with ⟨owner, inclusion⟩
    by_cases same : source = owner
    · subst owner
      simp only [findInclusion] at produced
      cases Option.some.inj produced
      exact List.mem_cons_self
    · simp only [findInclusion, dite_eq_right same] at produced
      exact List.mem_cons_of_mem _ (ih produced)

/-- A cache hit is an actual stored inclusion for the exact source context. -/
theorem InclusionCache.find?_mem {target source : Context registry}
    (cache : InclusionCache target) (found : Inclusion source target)
    (produced : cache.find? source = some found) :
    (⟨source, found⟩ : Σ owner : Context registry, Inclusion owner target) ∈ cache.entries :=
  findInclusion_mem cache.entries found produced

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

/-- Traverse original dependencies in order. Exact cached owners and checked
existing selected roots are reused before appending an algebraic level. -/
@[expose] def InclusionCache.rebuild? {target source : Context registry}
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
        match cache.findRoot? converted with
        | some matched =>
          let binding := SignDet.Descriptor.build_raw
            (SignDet.Descriptor.validate_eq_some.mp checked)
          let next := initial.reuseRoot descriptor converted binding matched
          (cache.insert next).rebuild? next rest
        | none =>
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

/-- Reusing a cached child follows its actual stored inclusion through the
remaining original suffix. -/
theorem InclusionCache.rebuild?_hit {target source : Context registry}
    (cache : InclusionCache target) (initial : Inclusion source target)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (rest : Suffix (source.adjoin descriptor).context)
    (found : Inclusion (source.adjoin descriptor).context target)
    (present : cache.find? (source.adjoin descriptor).context = some found) :
    cache.rebuild? initial (.root descriptor rest) = cache.rebuild? found rest := by
  simp only [InclusionCache.rebuild?, present]
  rfl

/-- A new root updates every cache entry through its actual target inclusion
before continuing through the remaining original suffix. -/
private theorem InclusionCache.rebuild?_miss_proof {target source : Context registry}
    (cache : InclusionCache target) (initial : Inclusion source target)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (rest : Suffix (source.adjoin descriptor).context)
    (missing : cache.find? (source.adjoin descriptor).context = none)
    (converted : SignDet.Descriptor target.Value Signature target.sign target.signature)
    (checked : SignDet.Descriptor.validate target.sign target.signature
      (source.mapDescriptor target initial.value descriptor) = some converted)
    (unmatched : cache.findRoot? converted = none) :
    cache.rebuild? initial (.root descriptor rest) =
      let child := target.adjoin converted
      let previous : Inclusion target child.context :=
        ⟨Conversion.includeRoot target converted child rfl,
          (Conversion.includeRoot_spec target converted child rfl).1⟩
      let next : Inclusion (source.adjoin descriptor).context child.context :=
        ⟨initial.native.adjoinCached descriptor converted checked child rfl,
          (initial.native.adjoinCached_spec descriptor converted checked child rfl).1⟩
      let updated := ((cache.extend previous).insert next).insert (Inclusion.identity child.context)
      (updated.rebuild? next rest).map fun later =>
        ⟨later.target, previous.comp later.inclusion, later.original, later.cache,
          later.base_eq.trans (by rw [Context.origin_adjoin, Origin.snoc_base])⟩ := by
  simp only [InclusionCache.rebuild?, missing]
  split
  · rename_i rejected
    rw [checked] at rejected
    contradiction
  · rename_i actual accepted
    have same : actual = converted := Option.some.inj (accepted.symm.trans checked)
    subst actual
    simp only [unmatched]
    split <;> rename_i recursiveProduced <;>
      simp only [recursiveProduced, Option.map]

private theorem InclusionCache.rebuild?_reuse_proof {target source : Context registry}
    (cache : InclusionCache target) (initial : Inclusion source target)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (rest : Suffix (source.adjoin descriptor).context)
    (missing : cache.find? (source.adjoin descriptor).context = none)
    (converted : SignDet.Descriptor target.Value Signature target.sign target.signature)
    (checked : SignDet.Descriptor.validate target.sign target.signature
      (source.mapDescriptor target initial.value descriptor) = some converted)
    (matched : RootMatch target converted)
    (present : cache.findRoot? converted = some matched) :
    cache.rebuild? initial (.root descriptor rest) =
      let binding := SignDet.Descriptor.build_raw
        (SignDet.Descriptor.validate_eq_some.mp checked)
      let next := initial.reuseRoot descriptor converted binding matched
      (cache.insert next).rebuild? next rest := by
  simp only [InclusionCache.rebuild?, missing]
  split
  · rename_i rejected
    rw [checked] at rejected
    contradiction
  · rename_i actual accepted
    have same : actual = converted := Option.some.inj (accepted.symm.trans checked)
    subst actual
    simp only [present]
    rfl

/-- A matching selected root registers the new owner in the unchanged target
and then traverses its remaining dependencies. -/
theorem InclusionCache.rebuild?_reuse {target source : Context registry}
    (cache : InclusionCache target) (initial : Inclusion source target)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (rest : Suffix (source.adjoin descriptor).context)
    (missing : cache.find? (source.adjoin descriptor).context = none)
    (converted : SignDet.Descriptor target.Value Signature target.sign target.signature)
    (checked : SignDet.Descriptor.validate target.sign target.signature
      (source.mapDescriptor target initial.value descriptor) = some converted)
    (matched : RootMatch target converted)
    (present : cache.findRoot? converted = some matched) :
    cache.rebuild? initial (.root descriptor rest) =
      let binding := SignDet.Descriptor.build_raw
        (SignDet.Descriptor.validate_eq_some.mp checked)
      let next := initial.reuseRoot descriptor converted binding matched
      (cache.insert next).rebuild? next rest :=
  cache.rebuild?_reuse_proof initial descriptor rest missing converted checked matched present

/-- A new validated root updates the cache before the remaining rebuild. -/
theorem InclusionCache.rebuild?_miss {target source : Context registry}
    (cache : InclusionCache target) (initial : Inclusion source target)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (rest : Suffix (source.adjoin descriptor).context)
    (missing : cache.find? (source.adjoin descriptor).context = none)
    (converted : SignDet.Descriptor target.Value Signature target.sign target.signature)
    (checked : SignDet.Descriptor.validate target.sign target.signature
      (source.mapDescriptor target initial.value descriptor) = some converted)
    (unmatched : cache.findRoot? converted = none) :
    cache.rebuild? initial (.root descriptor rest) =
      let child := target.adjoin converted
      let previous : Inclusion target child.context :=
        ⟨Conversion.includeRoot target converted child rfl,
          (Conversion.includeRoot_spec target converted child rfl).1⟩
      let next : Inclusion (source.adjoin descriptor).context child.context :=
        ⟨initial.native.adjoinCached descriptor converted checked child rfl,
          (initial.native.adjoinCached_spec descriptor converted checked child rfl).1⟩
      let updated := ((cache.extend previous).insert next).insert (Inclusion.identity child.context)
      (updated.rebuild? next rest).map fun later =>
        ⟨later.target, previous.comp later.inclusion, later.original, later.cache,
          later.base_eq.trans (by rw [Context.origin_adjoin, Origin.snoc_base])⟩ :=
  cache.rebuild?_miss_proof initial descriptor rest missing converted checked unmatched

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

/-- info: 'Hex.RealClosure.Tower.InclusionCache.find?_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.InclusionCache.find?_mem
