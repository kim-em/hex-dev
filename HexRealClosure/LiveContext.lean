/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerCache
public import HexRealClosure.TowerEnlargement

public section

open scoped List

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry}

/-- Checked inclusions retaining the exact owners and order of a list of
original live contexts. -/
inductive Inclusions (target : Context registry) : List (Context registry) → Type 1 where
  | nil : Inclusions target []
  | cons {source : Context registry} {rest : List (Context registry)}
      (head : Inclusion source target) (tail : Inclusions target rest) :
      Inclusions target (source :: rest)

/-- Carry every original owner through one later checked inclusion. -/
@[expose] def Inclusions.extend {source target : Context registry} (next : Inclusion source target) :
    {owners : List (Context registry)} → Inclusions source owners → Inclusions target owners
  | [], .nil => .nil
  | _ :: _, .cons head tail => .cons (head.comp next) (tail.extend next)

/-- Append one new owner without changing the retained order. -/
@[expose] def Inclusions.snoc {target source : Context registry} :
    {owners : List (Context registry)} → Inclusions target owners → Inclusion source target →
      Inclusions target (owners ++ [source])
  | [], .nil, next => .cons next .nil
  | _ :: _, .cons head tail, next => .cons head (tail.snoc next)

/-- Retrieve the checked map for an original context by its position, keeping
its original value and polynomial types. -/
@[expose] def Inclusions.get {target : Context registry} {owners : List (Context registry)}
    (maps : Inclusions target owners) (index : Fin owners.length) :
    Inclusion (owners[index]) target :=
  match owners, maps with
  | [], .nil => nomatch index
  | _ :: _, .cons head tail =>
    match index with
    | ⟨0, _⟩ => head
    | ⟨n + 1, h⟩ => tail.get ⟨n, Nat.lt_of_succ_lt_succ h⟩

/-- Every original owner uses the composition with the same later inclusion. -/
theorem Inclusions.get_extend {source target : Context registry}
    {owners : List (Context registry)} (maps : Inclusions source owners)
    (next : Inclusion source target) (index : Fin owners.length) :
    (maps.extend next).get index = (maps.get index).comp next := by
  induction maps with
  | nil => nomatch index
  | cons head tail ih =>
    rcases index with ⟨index, valid⟩
    cases index with
    | zero => rfl
    | succ n => exact ih ⟨n, Nat.lt_of_succ_lt_succ valid⟩

/-- One immutable shared context and a checked inclusion for every original
live context. All coefficient ancestry is retained by the validated source
contexts; rebuilding visits it in predecessor order. -/
structure Shared (base : BaseContext.PackedContext registry)
    (owners : List (Context registry)) : Type 1 where
  private mk ::
  input : Conversion (Context.ofBase base)
  maps : Inclusions input.context owners
  base_eq : input.context.origin.base = base
  cache : InclusionCache input.context

/-- Begin in the actual declared staged base. -/
def Shared.empty (base : BaseContext.PackedContext registry) : Shared base [] :=
  ⟨Conversion.identity (Context.ofBase base), .nil, by
    rw [(Conversion.identity_spec _).1]
    cases base with
    | pack base =>
      change (Context.base base).origin.base = BaseContext.PackedContext.pack base
      rw [Context.origin_base]
      rfl, ⟨[], []⟩⟩

/-- Register one requested context, reusing exact original predecessors and
checked existing selected-root values before adjoining a new level. Update all
previous checked inclusions together. -/
def Shared.addOrigin? {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    {source : Context registry} (origin : Origin source) :
    Option (Shared base (owners ++ [source])) := by
  cases origin with
  | pack original suffix source_eq =>
    exact do
      let previous ← Inclusion.base? (.pack original) base
      let starting := previous.comp (Inclusion.mk shared.input rfl)
      let rebuilt ← shared.cache.rebuild? starting suffix
      let combined := ((Inclusion.mk shared.input rfl).comp rebuilt.inclusion).native
      let newest : Inclusion source rebuilt.target := source_eq ▸ rebuilt.original
      return ⟨combined, (shared.maps.extend rebuilt.inclusion).snoc newest,
        rebuilt.base_eq.trans shared.base_eq, rebuilt.cache⟩

/-- One actual registration retains the old target inclusion as executable
result data, together with the new owner and every earlier owner map. -/
structure Registration {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (original : Shared base owners)
    (source : Context registry) : Type 1 where
  private mk ::
  shared : Shared base (owners ++ [source])
  previous : Inclusion original.input.context shared.input.context
  newest : Inclusion source shared.input.context
  maps_eq : shared.maps = (original.maps.extend previous).snoc newest

/-- Rebuild an original owner's suffix from one already checked base inclusion.
The result retains the old target map, all owner maps and the updated cache. -/
private def Shared.registerBase? {base : BaseContext.PackedContext registry}
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

/-- Register once and return the actual maps for old computed values and the
new owner. The same cached rebuilding operation produces both. -/
def Shared.registerOrigin? {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    {source : Context registry} (origin : Origin source) :
    Option (Registration shared source) := do
  let previous ← Inclusion.base? origin.base base
  shared.registerBase? origin previous

/-- Register a live context and retain its actual executable target transport. -/
def Shared.register? {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (source : Context registry) : Option (Registration shared source) :=
  shared.registerOrigin? source.origin

/-- Forgetting the retained maps gives exactly the existing origin registration. -/
theorem Shared.registerOrigin?_shared {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    {source : Context registry} (origin : Origin source) :
    (shared.registerOrigin? origin).map Registration.shared = shared.addOrigin? origin := by
  cases origin with
  | pack original suffix same =>
    cases same
    simp only [Shared.registerOrigin?, Shared.registerBase?, Shared.addOrigin?, Origin.base]
    cases baseEq : Inclusion.base? (.pack original) base with
    | none => simp [baseEq]
    | some previous =>
      cases rebuiltEq : shared.cache.rebuild?
          (previous.comp (Inclusion.mk shared.input rfl)) suffix with
      | none => simp [baseEq, rebuiltEq]
      | some rebuilt => simp [baseEq, rebuiltEq]

/-- The retained-map producer has the same shared result as registration. -/
theorem Shared.register?_shared {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (source : Context registry) :
    (shared.register? source).map Registration.shared = shared.addOrigin? source.origin :=
  shared.registerOrigin?_shared source.origin

/-- A successful cached rebuild returns the exact registration packet's
conversion, predecessor map, owner family and cache. -/
private theorem Shared.registerBase?_spec {base : BaseContext.PackedContext registry}
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

/-- A successful cached rebuild supplies the actual retained-target inclusion,
new-owner map, input conversion and cache of the registration packet. -/
theorem Shared.registerOrigin?_spec {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (original : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base original)) {source : Context registry}
    (same : suffix.context = source)
    (previous : Inclusion (Context.base original) (Context.ofBase base))
    (baseProduced : Inclusion.base? (.pack original) base = some previous)
    (rebuilt : CacheResult shared.input.context suffix.context)
    (produced : shared.cache.rebuild?
      (previous.comp (Inclusion.mk shared.input rfl)) suffix = some rebuilt) :
    ∃ packet : Registration shared source,
      shared.registerOrigin? (.pack original suffix same) = some packet ∧
      packet.shared.input = ((Inclusion.mk shared.input rfl).comp rebuilt.inclusion).native ∧
      HEq packet.previous rebuilt.inclusion ∧
      HEq packet.shared.maps ((shared.maps.extend rebuilt.inclusion).snoc (_root_.cast
        (congrArg (fun context => Inclusion context rebuilt.target) same) rebuilt.original)) ∧
      HEq packet.shared.cache rebuilt.cache := by
  obtain ⟨packet, checked, inputEq, previousEq, mapsEq, cacheEq⟩ :=
    shared.registerBase?_spec original suffix same previous rebuilt produced
  refine ⟨packet, ?_, inputEq, previousEq, mapsEq, cacheEq⟩
  simp only [Shared.registerOrigin?, Origin.base, baseProduced, bind, Option.bind]
  exact checked

private theorem Shared.empty_input_proof (base : BaseContext.PackedContext registry) :
    (Shared.empty base).input = Conversion.identity (Context.ofBase base) := rfl

/-- The empty collection begins with the actual native identity conversion. -/
theorem Shared.empty_input (base : BaseContext.PackedContext registry) :
    (Shared.empty base).input = Conversion.identity (Context.ofBase base) :=
  Shared.empty_input_proof base

private theorem Shared.empty_entries_proof (base : BaseContext.PackedContext registry) :
    (Shared.empty base).cache.entries = [] := rfl

/-- The initial collection has no original predecessor cache entries. -/
theorem Shared.empty_entries (base : BaseContext.PackedContext registry) :
    (Shared.empty base).cache.entries = [] := Shared.empty_entries_proof base

private theorem Shared.empty_candidates_proof (base : BaseContext.PackedContext registry) :
    (Shared.empty base).cache.candidates = [] := rfl

/-- The empty shared collection has no algebraic candidate images. -/
theorem Shared.empty_candidates (base : BaseContext.PackedContext registry) :
    (Shared.empty base).cache.candidates = [] := Shared.empty_candidates_proof base

private theorem Shared.empty_maps_proof (base : BaseContext.PackedContext registry) :
    HEq (Shared.empty base).maps
      (Inclusions.nil (target := (Shared.empty base).input.context)) := HEq.rfl

/-- The initial collection has no original owner maps. -/
theorem Shared.empty_maps (base : BaseContext.PackedContext registry) :
    HEq (Shared.empty base).maps
      (Inclusions.nil (target := (Shared.empty base).input.context)) :=
  Shared.empty_maps_proof base

private theorem Shared.addOrigin?_spec_proof {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (original : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base original)) {source : Context registry}
    (same : suffix.context = source)
    (previous : Inclusion (Context.base original) (Context.ofBase base))
    (baseProduced : Inclusion.base? (.pack original) base = some previous)
    (rebuilt : CacheResult shared.input.context suffix.context)
    (produced : shared.cache.rebuild?
      (previous.comp (Inclusion.mk shared.input rfl)) suffix = some rebuilt) :
    ∃ result, shared.addOrigin? (.pack original suffix same) = some result ∧
      result.input = ((Inclusion.mk shared.input rfl).comp rebuilt.inclusion).native ∧
      HEq result.maps ((shared.maps.extend rebuilt.inclusion).snoc (_root_.cast (congrArg (fun context => Inclusion context rebuilt.target) same) rebuilt.original)) ∧
      HEq result.cache rebuilt.cache := by
  cases same
  refine ⟨⟨((Inclusion.mk shared.input rfl).comp rebuilt.inclusion).native,
    (shared.maps.extend rebuilt.inclusion).snoc rebuilt.original,
    rebuilt.base_eq.trans shared.base_eq, rebuilt.cache⟩, ?_, rfl, HEq.rfl, HEq.rfl⟩
  simp only [Shared.addOrigin?, baseProduced, bind, Option.bind, pure]
  rw (config := { transparency := .all }) [produced]

/-- Actual registration combines the returned predecessor inclusion with
all retained owners and the exact returned cache. -/
theorem Shared.addOrigin?_spec {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (original : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base original)) {source : Context registry}
    (same : suffix.context = source)
    (previous : Inclusion (Context.base original) (Context.ofBase base))
    (baseProduced : Inclusion.base? (.pack original) base = some previous)
    (rebuilt : CacheResult shared.input.context suffix.context)
    (produced : shared.cache.rebuild?
      (previous.comp (Inclusion.mk shared.input rfl)) suffix = some rebuilt) :
    ∃ result, shared.addOrigin? (.pack original suffix same) = some result ∧
      result.input = ((Inclusion.mk shared.input rfl).comp rebuilt.inclusion).native ∧
      HEq result.maps ((shared.maps.extend rebuilt.inclusion).snoc (_root_.cast (congrArg (fun context => Inclusion context rebuilt.target) same) rebuilt.original)) ∧
      HEq result.cache rebuilt.cache :=
  shared.addOrigin?_spec_proof original suffix same previous baseProduced rebuilt produced

/-- Register a validated context using its actual stored base and complete
root suffix, without caller-supplied coefficient or semantic agreement. -/
def Shared.add? {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (source : Context registry) : Option (Shared base (owners ++ [source])) :=
  shared.addOrigin? source.origin

/-- Registration extends every old owner through one shared inclusion and
appends the requested original context's checked inclusion. -/
theorem Shared.addOrigin?_maps {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    {source : Context registry} (origin : Origin source)
    (result : Shared base (owners ++ [source]))
    (produced : shared.addOrigin? origin = some result) :
    ∃ previous : Inclusion shared.input.context result.input.context,
      ∃ newest : Inclusion source result.input.context,
        result.maps = (shared.maps.extend previous).snoc newest := by
  cases origin with
  | pack original suffix source_eq =>
    cases source_eq
    cases base_eq : Inclusion.base? (.pack original) base with
    | none => simp [Shared.addOrigin?, base_eq] at produced
    | some previous =>
      let starting := previous.comp (Inclusion.mk shared.input rfl)
      cases rebuilt_eq : shared.cache.rebuild? starting suffix with
      | none => simp [Shared.addOrigin?, base_eq, starting, rebuilt_eq] at produced
      | some rebuilt =>
        simp only [starting] at rebuilt_eq
        simp only [Shared.addOrigin?, base_eq, bind, Option.bind, rebuilt_eq, pure] at produced
        cases Option.some.inj produced
        exact ⟨rebuilt.inclusion, rebuilt.original, rfl⟩

/-- The public registration API retains the original owner order and maps. -/
theorem Shared.add?_maps {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (source : Context registry) (result : Shared base (owners ++ [source]))
    (produced : shared.add? source = some result) :
    ∃ previous : Inclusion shared.input.context result.input.context,
      ∃ newest : Inclusion source result.input.context,
        result.maps = (shared.maps.extend previous).snoc newest :=
  shared.addOrigin?_maps source.origin result produced

/-- Transport one original value through its returned checked map. -/
@[expose] def Shared.value {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (index : Fin owners.length) (a : (owners[index]).Value) : shared.input.context.Value :=
  (shared.maps.get index).value a

/-- Transport all polynomial coefficients through the same original-owner map. -/
@[expose] def Shared.polynomial {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (index : Fin owners.length) (p : (owners[index]).Poly) : shared.input.context.Poly :=
  (shared.maps.get index).polynomial p

/-- Register a finite list in its original order. Every additional context
updates the maps of all contexts already registered. -/
def Shared.collect? {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners) :
    (later : List (Context registry)) → Option (Shared base (owners ++ later))
  | [] => some (_root_.cast (congrArg (Shared base) (List.append_nil owners).symm) shared)
  | source :: rest => do
    let added ← shared.add? source
    let result ← added.collect? rest
    return _root_.cast (congrArg (Shared base) (List.append_assoc owners [source] rest)) result

/-- Assemble a shared target from actual validated context handles. -/
def Shared.gather? (base : BaseContext.PackedContext registry)
    (owners : List (Context registry)) : Option (Shared base owners) :=
  (Shared.empty base).collect? owners

private theorem Shared.add?_eq_proof {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (source : Context registry) : shared.add? source = shared.addOrigin? source.origin := rfl

/-- Registration consumes the context's actual stored origin. -/
theorem Shared.add?_eq {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (source : Context registry) : shared.add? source = shared.addOrigin? source.origin := Shared.add?_eq_proof shared source

private theorem Shared.collect?_nil_proof {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners) :
    shared.collect? [] = some (_root_.cast
      (congrArg (Shared base) (List.append_nil owners).symm) shared) := rfl

private theorem Shared.register?_eq_proof {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (source : Context registry) :
    shared.register? source = shared.registerOrigin? source.origin := rfl

/-- Registration with retained maps consumes the same stored origin. -/
theorem Shared.register?_eq {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (source : Context registry) :
    shared.register? source = shared.registerOrigin? source.origin :=
  Shared.register?_eq_proof shared source

/-- The empty collection step only transports its owner-list index. -/
theorem Shared.collect?_nil {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners) :
    shared.collect? [] = some (_root_.cast
      (congrArg (Shared base) (List.append_nil owners).symm) shared) := Shared.collect?_nil_proof shared

private theorem Shared.collect?_cons_proof {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (source : Context registry) (rest : List (Context registry)) :
    shared.collect? (source :: rest) = do
      let added ← shared.add? source
      let result ← added.collect? rest
      return _root_.cast (congrArg (Shared base)
        (List.append_assoc owners [source] rest)) result := rfl

/-- Collection registers the next original owner before visiting the rest. -/
theorem Shared.collect?_cons {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (source : Context registry) (rest : List (Context registry)) :
    shared.collect? (source :: rest) = do
      let added ← shared.add? source
      let result ← added.collect? rest
      return _root_.cast (congrArg (Shared base)
        (List.append_assoc owners [source] rest)) result := Shared.collect?_cons_proof shared source rest

private theorem Shared.gather?_eq_proof (base : BaseContext.PackedContext registry)
    (owners : List (Context registry)) :
    Shared.gather? base owners = (Shared.empty base).collect? owners := rfl

/-- Gathering uses the declared base and the actual owner collection. -/
theorem Shared.gather?_eq (base : BaseContext.PackedContext registry)
    (owners : List (Context registry)) :
    Shared.gather? base owners = (Shared.empty base).collect? owners := Shared.gather?_eq_proof base owners

/-- One enlargement of the shared target, retaining every original owner and
returning the new positive parameter in that same target. -/
structure SharedEnlargement {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (original : Shared base owners) : Type 1 where
  private mk ::
  shared : Shared base.infinitesimal owners
  checked : Enlargement original.input.context
  context_eq : checked.conversion.context = shared.input.context

/-- The old shared target enters the exact target of the cached packet. -/
@[expose] def SharedEnlargement.previous {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} {original : Shared base owners}
    (result : SharedEnlargement original) :
    Inclusion original.input.context result.shared.input.context :=
  ⟨result.checked.conversion, result.context_eq⟩

/-- Read the cached parameter in the returned shared context. -/
@[expose] def SharedEnlargement.parameter {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} {original : Shared base owners}
    (result : SharedEnlargement original) : result.shared.input.context.Value :=
  _root_.cast (congrArg Context.Value result.context_eq) result.checked.parameter

/-- Rebuild the shared suffix once over the next staged base. All registered
inclusions enter the returned context through the same checked conversion. -/
def Shared.enlargeOrigin? {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (origin : Origin shared.input.context) : Option (SharedEnlargement shared) := by
  cases origin with
  | pack original suffix source_eq =>
    have original_eq : BaseContext.PackedContext.pack original = base :=
      (Suffix.origin_base original suffix).symm.trans
        ((congrArg (fun context => context.origin.base) source_eq).trans shared.base_eq)
    cases original_eq
    exact do
      let initial := Conversion.infinitesimal original
      let rebuilt ← initial.rebuild? suffix
      let converted := rebuilt.result.cast source_eq
      let input := rebuilt.input.cast (Conversion.infinitesimal_spec original).1
      let same : input.context = converted.context :=
        (rebuilt.input.cast_spec (Conversion.infinitesimal_spec original).1).1.trans
          (rebuilt.input_spec.1.trans (rebuilt.result.cast_spec source_eq).1.symm)
      let next : Conversion (Context.ofBase (.pack original.infinitesimal)) := input
      have returned_base : next.context.origin.base =
          BaseContext.PackedContext.pack original.infinitesimal := by
        exact (congrArg (fun context => context.origin.base)
          ((rebuilt.input.cast_spec (Conversion.infinitesimal_spec original).1).1.trans
            (rebuilt.input_spec.1.trans rebuilt.context_eq.symm))).trans
          (rebuilt.suffix.base_eq.trans (by
            rw [(Conversion.infinitesimal_spec original).1, Context.origin_base]))
      let target : Inclusion shared.input.context next.context :=
        ⟨converted, same.symm⟩
      have native_eq : rebuilt.suffix.context = next.context :=
        rebuilt.context_eq.trans (rebuilt.input_spec.1.symm.trans
          (rebuilt.input.cast_spec (Conversion.infinitesimal_spec original).1).1.symm)
      let native : InclusionCache next.context := native_eq ▸ rebuilt.suffix.prefixes.cache
      let enlarged : Shared (.pack original.infinitesimal) owners :=
        ⟨next, shared.maps.extend target, returned_base,
          native.append (shared.cache.extend target)⟩
      return ⟨enlarged, rebuilt.enlargement original source_eq,
        (rebuilt.enlargement_conversion original source_eq).symm ▸ same.symm⟩

/-- Enlarge the actual stored shared context and update all its checked maps. -/
def Shared.enlarge? {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners) :
    Option (SharedEnlargement shared) := shared.enlargeOrigin? shared.input.context.origin

/-- The collection retains the existing producer's complete checked packet,
with no second suffix reconstruction. -/
theorem Shared.enlargeOrigin?_checked {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (origin : Origin shared.input.context) :
    (shared.enlargeOrigin? origin).map (fun result => result.checked) =
      origin.enlargeWithParameter? := by
  cases origin with
  | pack original suffix source_eq =>
    have original_eq : BaseContext.PackedContext.pack original = base :=
      (Suffix.origin_base original suffix).symm.trans
        ((congrArg (fun context => context.origin.base) source_eq).trans shared.base_eq)
    cases original_eq
    simp only [Shared.enlargeOrigin?, Origin.enlargeWithParameter?]
    cases (Conversion.infinitesimal original).rebuild? suffix <;> rfl

/-- A successful enlargement updates every retained owner through its one
returned inclusion of the old shared target. -/
theorem Shared.enlargeOrigin?_maps {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (origin : Origin shared.input.context) (result : SharedEnlargement shared)
    (produced : shared.enlargeOrigin? origin = some result) :
    result.shared.maps = shared.maps.extend result.previous := by
  cases origin with
  | pack original suffix source_eq =>
    have original_eq : BaseContext.PackedContext.pack original = base :=
      (Suffix.origin_base original suffix).symm.trans
        ((congrArg (fun context => context.origin.base) source_eq).trans shared.base_eq)
    cases original_eq
    cases rebuilt_eq : (Conversion.infinitesimal original).rebuild? suffix with
    | none =>
      simp only [Shared.enlargeOrigin?, rebuilt_eq] at produced
      change none = some result at produced
      cases produced
    | some rebuilt =>
      simp only [Shared.enlargeOrigin?, rebuilt_eq] at produced
      cases Option.some.inj produced
      simp only [SharedEnlargement.previous, Rebuilt.enlargement_conversion]

/-- The public producer updates all retained maps through its shared inclusion. -/
theorem Shared.enlarge?_maps {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (result : SharedEnlargement shared) (produced : shared.enlarge? = some result) :
    result.shared.maps = shared.maps.extend result.previous :=
  shared.enlargeOrigin?_maps _ result produced

/-- Every returned owner map is the old map followed by the shared inclusion. -/
theorem Shared.enlarge?_owner {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (result : SharedEnlargement shared) (produced : shared.enlarge? = some result)
    (index : Fin owners.length) :
    result.shared.maps.get index = (shared.maps.get index).comp result.previous := by
  rw [shared.enlargeOrigin?_maps _ result produced]
  exact Inclusions.get_extend _ _ _

/-- Each original value follows its retained owner map through enlargement. -/
theorem Shared.enlarge?_value {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (result : SharedEnlargement shared) (produced : shared.enlarge? = some result)
    (index : Fin owners.length) (a : (owners[index]).Value) :
    result.shared.value index a = result.previous.value (shared.value index a) := by
  unfold Shared.value
  rw [shared.enlarge?_owner result produced index, Inclusion.comp_value]

/-- Collection enlargement returns the actual whole-context checked packet. -/
theorem Shared.enlarge?_checked {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners) :
    shared.enlarge?.map (fun result => result.checked) =
      shared.input.context.enlargeWithParameter? := shared.enlargeOrigin?_checked _

/-- Forgetting the collection maps returns the existing enlargement of the
entire shared context, with no second suffix reconstruction. -/
theorem Shared.enlargeOrigin?_conversion {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (origin : Origin shared.input.context) :
    (shared.enlargeOrigin? origin).map (fun result => result.previous.conversion) =
      origin.enlarge? := by
  have exact_packet := congrArg (fun packet => packet.map Enlargement.conversion)
    (shared.enlargeOrigin?_checked origin)
  have exact_conversion : origin.enlargeWithParameter?.map Enlargement.conversion =
      origin.enlarge? := by
    cases origin with
    | pack original suffix source_eq =>
      simp only [Origin.enlargeWithParameter?, Origin.enlarge?, ← Conversion.rebuild_result,
        Option.map_map, Function.comp_def, Rebuilt.enlargement_conversion]
  have aligned : (shared.enlargeOrigin? origin).map
      (fun result => result.previous.conversion) =
        origin.enlargeWithParameter?.map Enlargement.conversion := by
    simpa only [Option.map_map, Function.comp_def, SharedEnlargement.previous] using exact_packet
  exact aligned.trans exact_conversion

/-- Collection enlargement uses exactly the existing whole-context producer. -/
theorem Shared.enlarge?_conversion {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners) :
    shared.enlarge?.map (fun result => result.previous.conversion) =
      shared.input.context.enlarge? := shared.enlargeOrigin?_conversion _

/-- Registering the checked collection maps adds no failure to the existing
whole-context enlargement. -/
theorem Shared.enlarge?_isSome {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners) :
    shared.enlarge?.isSome = shared.input.context.enlarge?.isSome := by
  simpa only [Option.isSome_map] using congrArg Option.isSome shared.enlarge?_conversion

/-- Successful origin registration implies the actual base compatibility
checked by the producer; it is not an extra reader premise. -/
theorem Shared.addOrigin?_compatible {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    {source : Context registry} (origin : Origin source)
    (result : Shared base (owners ++ [source]))
    (produced : shared.addOrigin? origin = some result) :
    origin.base.signature.constants <+ base.signature.constants ∧
      origin.base.signature.infinitesimals ≤ base.signature.infinitesimals := by
  cases origin with
  | pack original suffix same =>
    apply (Inclusion.base?_isSome (.pack original) base).mp
    cases checked : Inclusion.base? (.pack original) base with
    | none => simp [Shared.addOrigin?, checked] at produced
    | some inclusion => rfl

/-- Successful registration carries its source's staged compatibility. -/
theorem Shared.add?_compatible {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (source : Context registry) (result : Shared base (owners ++ [source]))
    (produced : shared.add? source = some result) :
    source.origin.base.signature.constants <+ base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals := by
  rw [Shared.add?_eq] at produced
  exact shared.addOrigin?_compatible source.origin result produced

/-- Successful collection proves compatibility for every requested original
owner, including owners that were already present in the cache. -/
theorem Shared.collect?_compatible {base : BaseContext.PackedContext registry}
    {owners : List (Context registry)} (shared : Shared base owners)
    (later : List (Context registry)) (result : Shared base (owners ++ later))
    (produced : shared.collect? later = some result) :
    ∀ source ∈ later,
      source.origin.base.signature.constants <+ base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals := by
  induction later generalizing owners with
  | nil => simp
  | cons source rest ih =>
    rw [Shared.collect?_cons] at produced
    cases first : shared.add? source with
    | none => simp only [first, bind, Option.bind] at produced; contradiction
    | some added =>
      cases following : added.collect? rest with
      | none => simp only [first, following, bind, Option.bind] at produced; contradiction
      | some collected =>
        intro owner present
        rcases List.mem_cons.mp present with equal | present
        · subst owner
          exact shared.add?_compatible source added first
        · exact ih added collected following owner present

/-- A successful native gather already certifies every owner's staged base
compatibility. Readers need not supply it again. -/
theorem Shared.gather?_compatible (base : BaseContext.PackedContext registry)
    (owners : List (Context registry)) (shared : Shared base owners)
    (produced : Shared.gather? base owners = some shared) :
    ∀ source ∈ owners,
      source.origin.base.signature.constants <+ base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals := by
  rw [Shared.gather?_eq] at produced
  exact (Shared.empty base).collect?_compatible owners shared produced

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Shared.add?_maps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.add?_maps

/-- info: 'Hex.RealClosure.Tower.Shared.enlarge?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.enlarge?

/-- info: 'Hex.RealClosure.Tower.Shared.enlarge?_conversion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.enlarge?_conversion

/-- info: 'Hex.RealClosure.Tower.Shared.enlarge?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.enlarge?_isSome

/-- info: 'Hex.RealClosure.Tower.Shared.enlarge?_checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.enlarge?_checked

/-- info: 'Hex.RealClosure.Tower.Shared.enlarge?_owner' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.enlarge?_owner

/-- info: 'Hex.RealClosure.Tower.Shared.enlarge?_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.enlarge?_value

/-- info: 'Hex.RealClosure.Tower.Shared.addOrigin?_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.addOrigin?_spec
