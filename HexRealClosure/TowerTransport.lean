/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerRefinement

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry}

/-- A finite derivation of native conversion from identity, a new base
infinitesimal, a root inclusion, a checked root refinement, and rebuilt later levels.
This is erased provenance, not a semantic arithmetic law record. -/
inductive Transport : (source target : Context registry) → (source.Value → target.Value) → Prop
  | identity (context : Context registry) : Transport context context id
  | infinitesimal {K : Type} [Lean.Grind.Field K] [DecidableEq K] {sign : K → Int}
      (context : BaseContext.Context registry K sign) :
      Transport (Context.base context) (Context.base context.infinitesimal)
        BaseContext.Element.embed
  | inclusion (parent : Context registry)
      (descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature)
      (extension : Extension parent descriptor) (built : extension = parent.adjoin descriptor) :
      Transport parent extension.context extension.embed
  | refine (parent : Context registry)
      {source : SignDet.Descriptor parent.Value Signature parent.sign parent.signature}
      {head : DensePoly parent.Value} {lower upper : Endpoint parent.Value}
      (encoding : SignDet.Reencoding source head lower upper) :
      Transport (parent.adjoin source).context (parent.refine encoding).extension.context
        (parent.refine encoding).transport
  | adjoin {source target : Context registry} {value : source.Value → target.Value}
      (previous : Transport source target value)
      (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
      (converted : SignDet.Descriptor target.Value Signature target.sign target.signature)
      (binding : converted.raw = source.mapDescriptor target value descriptor) :
      Transport (source.adjoin descriptor).context (target.adjoin converted).context
        (fun x => target.ofPoly converted
          (DensePoly.ofCoeffs ((source.polynomial descriptor x).toArray.map value)))

  | comp {source middle target : Context registry}
      {first : source.Value → middle.Value} {next : middle.Value → target.Value}
      (left : Transport source middle first) (right : Transport middle target next) :
      Transport source target (fun x => next (first x))

/-- An immutable target context and its actual native conversion from a source.
The erased proof records the native steps used to construct it. -/
structure Conversion (source : Context registry) : Type 1 where
  private mk ::
  context : Context registry
  value : source.Value → context.Value
  checked : Transport source context value

/-- Start conversion without changing the context. -/
def Conversion.identity (source : Context registry) : Conversion source :=
  ⟨source, id, .identity source⟩

/-- Include a predecessor in one actual cached root extension. This records
the native coefficient embedding for subsequent common-context transport. -/
def Conversion.includeRoot (parent : Context registry)
    (descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature)
    (extension : Extension parent descriptor) (built : extension = parent.adjoin descriptor) :
    Conversion parent :=
  ⟨extension.context, extension.embed, .inclusion parent descriptor extension built⟩

private theorem Conversion.includeRoot_spec_proof (parent : Context registry)
    (descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature)
    (extension : Extension parent descriptor) (built : extension = parent.adjoin descriptor) :
    (Conversion.includeRoot parent descriptor extension built).context = extension.context ∧
      HEq (Conversion.includeRoot parent descriptor extension built).value extension.embed :=
  ⟨rfl, HEq.rfl⟩

/-- Root inclusion retains the cached child and its actual embedding closure. -/
theorem Conversion.includeRoot_spec (parent : Context registry)
    (descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature)
    (extension : Extension parent descriptor) (built : extension = parent.adjoin descriptor) :
    (Conversion.includeRoot parent descriptor extension built).context = extension.context ∧
      HEq (Conversion.includeRoot parent descriptor extension built).value extension.embed :=
  Conversion.includeRoot_spec_proof parent descriptor extension built

/-- Enlarge a completed base by one positive infinitesimal. Existing base
values enter through the native constant-rational-function embedding. -/
def Conversion.infinitesimal {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {sign : K → Int} (context : BaseContext.Context registry K sign) :
    Conversion (Context.base context) :=
  ⟨Context.base context.infinitesimal, BaseContext.Element.embed,
    .infinitesimal context⟩

/-- The base conversion retains the native next-base context and its actual
constant-rational-function embedding. -/
theorem Conversion.infinitesimal_spec {K : Type} [Lean.Grind.Field K] [DecidableEq K]
    {sign : K → Int} (context : BaseContext.Context registry K sign) :
    (Conversion.infinitesimal context).context = Context.base context.infinitesimal ∧
      HEq (Conversion.infinitesimal context).value
        (BaseContext.Element.embed : (Context.base context).Value →
          (Context.base context.infinitesimal).Value) :=
  ⟨rfl, HEq.rfl⟩

/-- Compose two actual native conversions, retaining both packing closures. -/
def Conversion.comp {source : Context registry} (first : Conversion source)
    (next : Conversion first.context) : Conversion source :=
  ⟨next.context, fun x => next.value (first.value x), .comp first.checked next.checked⟩

/-- Reconcile source ownership using a proved equality of immutable contexts.
The actual target and value closure are retained. -/
@[expose] def Conversion.cast {source other : Context registry}
    (conversion : Conversion source) (h : source = other) : Conversion other := h ▸ conversion

/-- Changing source ownership by equality retains the actual target and values. -/
theorem Conversion.cast_spec {source other : Context registry}
    (conversion : Conversion source) (h : source = other) :
    (conversion.cast h).context = conversion.context ∧
      HEq (conversion.cast h).value (fun x : other.Value =>
        conversion.value (_root_.cast (congrArg Context.Value h.symm) x)) := by
  cases h
  exact ⟨rfl, HEq.rfl⟩

private theorem Conversion.identity_spec_proof (source : Context registry) :
    (Conversion.identity source).context = source ∧ HEq (Conversion.identity source).value (id : source.Value → source.Value) :=
  ⟨rfl, HEq.rfl⟩

/-- Identity retains the original context and its values. -/
theorem Conversion.identity_spec (source : Context registry) :
    (Conversion.identity source).context = source ∧ HEq (Conversion.identity source).value (id : source.Value → source.Value) :=
  Conversion.identity_spec_proof source

private theorem Conversion.comp_spec_proof {source : Context registry} (first : Conversion source)
    (next : Conversion first.context) :
    (first.comp next).context = next.context ∧
      HEq (first.comp next).value (fun x => next.value (first.value x)) := ⟨rfl, HEq.rfl⟩

/-- Composition uses exactly the two returned native value conversions. -/
theorem Conversion.comp_spec {source : Context registry} (first : Conversion source)
    (next : Conversion first.context) :
    (first.comp next).context = next.context ∧
      HEq (first.comp next).value (fun x => next.value (first.value x)) :=
  Conversion.comp_spec_proof first next

/-- Start conversion at a checked persistent root refinement. -/
def Conversion.refine (parent : Context registry)
    {source : SignDet.Descriptor parent.Value Signature parent.sign parent.signature}
    {head : DensePoly parent.Value} {lower upper : Endpoint parent.Value}
    (encoding : SignDet.Reencoding source head lower upper) :
    Conversion (parent.adjoin source).context :=
  ⟨(parent.refine encoding).extension.context, (parent.refine encoding).transport,
    .refine parent encoding⟩

/-- Repack an old root context using the supplied actual converted child.
The validation and cached-child equality are erased construction evidence. -/
def Conversion.adjoinCached {source : Context registry} (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (converted : SignDet.Descriptor conversion.context.Value Signature
      conversion.context.sign conversion.context.signature)
    (h : SignDet.Descriptor.validate conversion.context.sign conversion.context.signature
      (source.mapDescriptor conversion.context conversion.value descriptor) = some converted)
    (extension : Extension conversion.context converted)
    (built : extension = conversion.context.adjoin converted) :
    Conversion (source.adjoin descriptor).context :=
  ⟨extension.context,
    fun x => extension.pack
      (DensePoly.ofCoeffs ((source.polynomial descriptor x).toArray.map conversion.value)), by
    cases built
    exact .adjoin conversion.checked descriptor converted
      (SignDet.Descriptor.build_raw (SignDet.Descriptor.validate_eq_some.mp h))⟩

private theorem Conversion.adjoinCached_spec_proof {source : Context registry}
    (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (converted : SignDet.Descriptor conversion.context.Value Signature
      conversion.context.sign conversion.context.signature)
    (h : SignDet.Descriptor.validate conversion.context.sign conversion.context.signature
      (source.mapDescriptor conversion.context conversion.value descriptor) = some converted)
    (extension : Extension conversion.context converted)
    (built : extension = conversion.context.adjoin converted) :
    (conversion.adjoinCached descriptor converted h extension built).context = extension.context ∧
      HEq (conversion.adjoinCached descriptor converted h extension built).value
        (fun x => conversion.context.ofPoly converted
          (DensePoly.ofCoeffs ((source.polynomial descriptor x).toArray.map conversion.value))) := by
  cases built
  exact ⟨rfl, HEq.rfl⟩

/-- Cached transport retains the actual child and its native packing closure. -/
theorem Conversion.adjoinCached_spec {source : Context registry}
    (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (converted : SignDet.Descriptor conversion.context.Value Signature
      conversion.context.sign conversion.context.signature)
    (h : SignDet.Descriptor.validate conversion.context.sign conversion.context.signature
      (source.mapDescriptor conversion.context conversion.value descriptor) = some converted)
    (extension : Extension conversion.context converted)
    (built : extension = conversion.context.adjoin converted) :
    (conversion.adjoinCached descriptor converted h extension built).context = extension.context ∧
      HEq (conversion.adjoinCached descriptor converted h extension built).value
        (fun x => conversion.context.ofPoly converted
          (DensePoly.ofCoeffs ((source.polynomial descriptor x).toArray.map conversion.value))) :=
  conversion.adjoinCached_spec_proof descriptor converted h extension built

/-- One native conversion step constructs its validated converted child. -/
def Conversion.adjoinChecked {source : Context registry} (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (converted : SignDet.Descriptor conversion.context.Value Signature
      conversion.context.sign conversion.context.signature)
    (h : SignDet.Descriptor.validate conversion.context.sign conversion.context.signature
      (source.mapDescriptor conversion.context conversion.value descriptor) = some converted) :
    Conversion (source.adjoin descriptor).context :=
  let extension := conversion.context.adjoin converted
  let pack := extension.pack
  ⟨extension.context,
    fun x => pack
      (DensePoly.ofCoeffs ((source.polynomial descriptor x).toArray.map conversion.value)),
    .adjoin conversion.checked descriptor converted
      (SignDet.Descriptor.build_raw (SignDet.Descriptor.validate_eq_some.mp h))⟩

private theorem Conversion.adjoinChecked_context_proof {source : Context registry}
    (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (converted : SignDet.Descriptor conversion.context.Value Signature
      conversion.context.sign conversion.context.signature)
    (h : SignDet.Descriptor.validate conversion.context.sign conversion.context.signature
      (source.mapDescriptor conversion.context conversion.value descriptor) = some converted) :
    (conversion.adjoinChecked descriptor converted h).context =
      (conversion.context.adjoin converted).context := rfl

/-- The validated step creates exactly the child of the converted descriptor. -/
theorem Conversion.adjoinChecked_context {source : Context registry}
    (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (converted : SignDet.Descriptor conversion.context.Value Signature
      conversion.context.sign conversion.context.signature)
    (h : SignDet.Descriptor.validate conversion.context.sign conversion.context.signature
      (source.mapDescriptor conversion.context conversion.value descriptor) = some converted) :
    (conversion.adjoinChecked descriptor converted h).context =
      (conversion.context.adjoin converted).context :=
  conversion.adjoinChecked_context_proof descriptor converted h

private theorem Conversion.adjoinChecked_value_proof {source : Context registry}
    (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (converted : SignDet.Descriptor conversion.context.Value Signature
      conversion.context.sign conversion.context.signature)
    (h : SignDet.Descriptor.validate conversion.context.sign conversion.context.signature
      (source.mapDescriptor conversion.context conversion.value descriptor) = some converted) :
    HEq (conversion.adjoinChecked descriptor converted h).value
      (fun x => conversion.context.ofPoly converted
        (DensePoly.ofCoeffs ((source.polynomial descriptor x).toArray.map conversion.value))) :=
  HEq.rfl

/-- The validated step repacks the actual converted polynomial. -/
theorem Conversion.adjoinChecked_value {source : Context registry}
    (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (converted : SignDet.Descriptor conversion.context.Value Signature
      conversion.context.sign conversion.context.signature)
    (h : SignDet.Descriptor.validate conversion.context.sign conversion.context.signature
      (source.mapDescriptor conversion.context conversion.value descriptor) = some converted) :
    HEq (conversion.adjoinChecked descriptor converted h).value
      (fun x => conversion.context.ofPoly converted
        (DensePoly.ofCoeffs ((source.polynomial descriptor x).toArray.map conversion.value))) :=
  conversion.adjoinChecked_value_proof descriptor converted h

/-- Rebuild one more later root and convert all values at that level. Repeating
this operation rebuilds any finite list of later levels without changing old contexts. -/
def Conversion.adjoin? {source : Context registry} (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature) :
    Option (Conversion (source.adjoin descriptor).context) :=
  match h : SignDet.Descriptor.validate conversion.context.sign conversion.context.signature
      (source.mapDescriptor conversion.context conversion.value descriptor) with
  | none => none
  | some converted => some (conversion.adjoinChecked descriptor converted h)

private theorem Conversion.refine_spec_proof (parent : Context registry)
    {source : SignDet.Descriptor parent.Value Signature parent.sign parent.signature}
    {head : DensePoly parent.Value} {lower upper : Endpoint parent.Value}
    (encoding : SignDet.Reencoding source head lower upper) :
    (Conversion.refine parent encoding).context = (parent.refine encoding).extension.context ∧
      HEq (Conversion.refine parent encoding).value (parent.refine encoding).transport :=
  ⟨rfl, HEq.rfl⟩

/-- The conversion starts with exactly the checked native refinement. -/
theorem Conversion.refine_spec (parent : Context registry)
    {source : SignDet.Descriptor parent.Value Signature parent.sign parent.signature}
    {head : DensePoly parent.Value} {lower upper : Endpoint parent.Value}
    (encoding : SignDet.Reencoding source head lower upper) :
    (Conversion.refine parent encoding).context = (parent.refine encoding).extension.context ∧
      HEq (Conversion.refine parent encoding).value (parent.refine encoding).transport :=
  Conversion.refine_spec_proof parent encoding

private theorem Conversion.adjoin_spec_proof {source : Context registry}
    (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (result : Conversion (source.adjoin descriptor).context)
    (h : conversion.adjoin? descriptor = some result) :
    ∃ converted : SignDet.Descriptor conversion.context.Value Signature
        conversion.context.sign conversion.context.signature,
      converted.raw = source.mapDescriptor conversion.context conversion.value descriptor ∧
      result.context = (conversion.context.adjoin converted).context ∧
      HEq result.value (fun x => conversion.context.ofPoly converted
        (DensePoly.ofCoeffs ((source.polynomial descriptor x).toArray.map conversion.value))) := by
  unfold Conversion.adjoin? at h
  split at h
  · contradiction
  · rename_i converted hc
    cases h
    exact ⟨converted, SignDet.Descriptor.build_raw (SignDet.Descriptor.validate_eq_some.mp hc),
      rfl, HEq.rfl⟩

/-- A successful later extension binds the actual converted operands and
captures the native packing operation used for every value. -/
theorem Conversion.adjoin_spec {source : Context registry}
    (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (result : Conversion (source.adjoin descriptor).context)
    (h : conversion.adjoin? descriptor = some result) :
    ∃ converted : SignDet.Descriptor conversion.context.Value Signature
        conversion.context.sign conversion.context.signature,
      converted.raw = source.mapDescriptor conversion.context conversion.value descriptor ∧
      result.context = (conversion.context.adjoin converted).context ∧
      HEq result.value (fun x => conversion.context.ofPoly converted
        (DensePoly.ofCoeffs ((source.polynomial descriptor x).toArray.map conversion.value))) :=
  Conversion.adjoin_spec_proof conversion descriptor result h

private theorem Conversion.adjoin_exists_proof {source : Context registry}
    (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (h : ∃ converted, SignDet.Descriptor.validate conversion.context.sign conversion.context.signature
      (source.mapDescriptor conversion.context conversion.value descriptor) = some converted) :
    ∃ result, conversion.adjoin? descriptor = some result := by
  obtain ⟨converted, h⟩ := h
  unfold Conversion.adjoin?
  split
  · rename_i hn
    cases hn.symm.trans h
  · exact ⟨_, rfl⟩

/-- Successful descriptor revalidation produces a checked native conversion. -/
theorem Conversion.adjoin_exists {source : Context registry}
    (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (h : ∃ converted, SignDet.Descriptor.validate conversion.context.sign conversion.context.signature
      (source.mapDescriptor conversion.context conversion.value descriptor) = some converted) :
    ∃ result, conversion.adjoin? descriptor = some result :=
  Conversion.adjoin_exists_proof conversion descriptor h

/-- A finite suffix of validated root extensions over an immutable predecessor. -/
inductive Suffix : Context registry → Type 1 where
  | nil {source : Context registry} : Suffix source
  | root {source : Context registry}
      (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
      (rest : Suffix (source.adjoin descriptor).context) : Suffix source

/-- The original final context, with all later roots still valid. -/
@[expose] def Suffix.context {source : Context registry} : Suffix source → Context registry
  | .nil => source
  | .root _ rest => rest.context

/-- Include a predecessor value through every actual root extension in a
validated suffix. The original value retains its original context. -/
@[expose] def Suffix.embed {source : Context registry} (suffix : Suffix source) :
    source.Value → suffix.context.Value :=
  match suffix with
  | .nil => id
  | .root descriptor rest =>
      let extension := source.adjoin descriptor
      let includeRest := rest.embed
      fun a => includeRest (extension.embed a)

/-- Rebuild every later level in order and return the final native conversion.
Each rebuilt level retains its packing closure and fresh descriptor evidence. -/
def Conversion.extend? {source : Context registry} (conversion : Conversion source)
    (suffix : Suffix source) : Option (Conversion suffix.context) :=
  match suffix with
  | .nil => some conversion
  | .root descriptor rest =>
    match conversion.adjoin? descriptor with
    | none => none
    | some next => next.extend? rest

private theorem Conversion.extend_nil_proof {source : Context registry} (conversion : Conversion source) :
    conversion.extend? .nil = some conversion := rfl

/-- An empty suffix retains the starting conversion. -/
theorem Conversion.extend_nil {source : Context registry} (conversion : Conversion source) :
    conversion.extend? .nil = some conversion := Conversion.extend_nil_proof conversion

private theorem Conversion.extend_root_proof {source : Context registry} (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (rest : Suffix (source.adjoin descriptor).context) :
    conversion.extend? (.root descriptor rest) =
      match conversion.adjoin? descriptor with
      | none => none
      | some next => next.extend? rest := rfl

/-- The executable follows the actual returned conversion at each later root. -/
theorem Conversion.extend_root {source : Context registry} (conversion : Conversion source)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (rest : Suffix (source.adjoin descriptor).context) :
    conversion.extend? (.root descriptor rest) =
      match conversion.adjoin? descriptor with
      | none => none
      | some next => next.extend? rest := Conversion.extend_root_proof conversion descriptor rest

/-- Native provenance for the exact descriptors returned by suffix rebuilding. -/
inductive Rebuilds : {source : Context registry} → (initial : Conversion source) →
    (original : Suffix source) → (result : Conversion original.context) →
    (suffix : Suffix initial.context) → Prop where
  | nil {source : Context registry} (initial : Conversion source) :
      Rebuilds initial .nil initial .nil
  | root {source : Context registry} (initial : Conversion source)
      (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
      (rest : Suffix (source.adjoin descriptor).context)
      (converted : SignDet.Descriptor initial.context.Value Signature
        initial.context.sign initial.context.signature)
      (h : SignDet.Descriptor.validate initial.context.sign initial.context.signature
        (source.mapDescriptor initial.context initial.value descriptor) = some converted)
      {result : Conversion rest.context}
      {suffix : Suffix (initial.adjoinChecked descriptor converted h).context}
      (tail : Rebuilds (initial.adjoinChecked descriptor converted h) rest result suffix) :
      Rebuilds initial (.root descriptor rest) result
        (.root converted (initial.adjoinChecked_context descriptor converted h ▸ suffix))

/-- Rebuilt later roots, retaining the new descriptors as well as the final
conversion. The equality binds the returned suffix to that conversion's
actual target context; the erased trace pins each descriptor to its validated
native step. -/
structure Rebuilt {source : Context registry} (initial : Conversion source)
    (original : Suffix source) : Type 1 where
  private mk ::
  result : Conversion original.context
  suffix : Suffix initial.context
  context_eq : suffix.context = result.context
  checked : Rebuilds initial original result suffix

/-- A rebuilt nonempty suffix starts with a validated converted root. -/
theorem Rebuilt.root_shape {source : Context registry} {initial : Conversion source}
    {descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature}
    {rest : Suffix (source.adjoin descriptor).context}
    (rebuilt : Rebuilt initial (.root descriptor rest)) :
    ∃ converted : SignDet.Descriptor initial.context.Value Signature
        initial.context.sign initial.context.signature,
      ∃ tail : Suffix (initial.context.adjoin converted).context,
        rebuilt.suffix = .root converted tail := by
  rcases rebuilt with ⟨result, suffix, context_eq, checked⟩
  cases checked with
  | root _ _ _ converted h tail =>
    exact ⟨converted, _, rfl⟩

/-- Rebuild every later root and retain its validated descriptor. The returned
suffix supplies checked executable inputs for another refinement. -/
def Conversion.rebuild? {source : Context registry} (conversion : Conversion source)
    (suffix : Suffix source) : Option (Rebuilt conversion suffix) :=
  match suffix with
  | .nil => some ⟨conversion, .nil, rfl, .nil conversion⟩
  | .root descriptor rest =>
    match h : SignDet.Descriptor.validate conversion.context.sign conversion.context.signature
        (source.mapDescriptor conversion.context conversion.value descriptor) with
    | none => none
    | some converted =>
      let next : Conversion (source.adjoin descriptor).context :=
        conversion.adjoinChecked descriptor converted h
      match next.rebuild? rest with
      | none => none
      | some rebuilt =>
        let same := conversion.adjoinChecked_context descriptor converted h
        some ⟨rebuilt.result, .root converted (same ▸ rebuilt.suffix),
          by cases same; exact rebuilt.context_eq,
          .root conversion descriptor rest converted h rebuilt.checked⟩

/-- Retaining rebuilt descriptors does not change the final native conversion
returned by the existing suffix traversal. -/
theorem Conversion.rebuild_result {source : Context registry}
    (conversion : Conversion source) (suffix : Suffix source) :
    (conversion.rebuild? suffix).map Rebuilt.result = conversion.extend? suffix := by
  induction suffix with
  | nil => rfl
  | root descriptor rest ih =>
    rename_i current
    simp only [Conversion.rebuild?, Conversion.extend?, Conversion.adjoin?]
    split
    · rfl
    · rename_i converted h
      let next : Conversion (current.adjoin descriptor).context :=
        conversion.adjoinChecked descriptor converted h
      cases hr : next.rebuild? rest with
      | none => simpa only [hr, Option.map, next, Suffix.context] using ih next
      | some rebuilt => simpa only [hr, Option.map, next, Suffix.context] using ih next

end Hex.RealClosure.Tower

/--
info: 'Hex.RealClosure.Tower.Conversion.extend?' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.extend?
/--
info: 'Hex.RealClosure.Tower.Conversion.comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.comp

/--
info: 'Hex.RealClosure.Tower.Conversion.cast' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.cast
/--
info: 'Hex.RealClosure.Tower.Conversion.cast_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.cast_spec

/-- info: 'Hex.RealClosure.Tower.Conversion.infinitesimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.infinitesimal

/-- info: 'Hex.RealClosure.Tower.Conversion.infinitesimal_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.infinitesimal_spec
