/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.ContextModel
public import HexRealClosureMathlib.LiveContext
public import HexRealClosureMathlib.TowerReuse
import all HexRealClosure.TowerCache

public section

namespace Hex.RealClosure.Tower.InclusionCache

variable {registry : BaseContext.Registry} {base : BaseContext.PackedContext registry}
variable {R : Type u} [Field R] [LinearOrder R] [DecidableEq R]
variable [IsStrictOrderedRing R] [IsRealClosed R]
variable (following : base.Realization) (reference : Tower.Model (Context.ofBase base) R)

/-- An actual cached inclusion preserves the canonical interpretation of its
original owner in the fixed target field. The owner model comes from the
provider-history factory, rather than an independently chosen interpretation. -/
structure EntryModel {source destination : Context registry}
    (target : Tower.Model destination R) (inclusion : Inclusion source destination) where
  original : Tower.Model source R
  produced : source.model? following reference = some original
  value : ∀ a, target.value (inclusion.value a) = original.value a

/-- Every actual cache entry has its factory-derived owner interpretation and
preserves values in the same target model. -/
@[expose] def Models {destination : Context registry} (target : Tower.Model destination R)
    (cache : InclusionCache destination) :=
  ∀ entry, entry ∈ cache.entries → EntryModel following reference target entry.2

variable {following reference}

/-- The identity cache entry retains the canonical target interpretation. -/
noncomputable def EntryModel.identity {source : Context registry}
    (target : Tower.Model source R)
    (produced : source.model? following reference = some target) :
    EntryModel following reference target (Inclusion.identity source) where
  original := target
  produced := produced
  value := by intro a; rw [Inclusion.identity_value]

/-- The exact cached native conversion preserves its canonical source model. -/
noncomputable def EntryModel.native {source destination : Context registry}
    {target : Tower.Model destination R} {inclusion : Inclusion source destination}
    (model : EntryModel following reference target inclusion) :
    Conversion.Model inclusion.native model.original where
  target := target
  value := model.value

private theorem EntryModel.native_target_proof {source destination : Context registry}
    {target : Tower.Model destination R} {inclusion : Inclusion source destination}
    (model : EntryModel following reference target inclusion) :
    model.native.target = target := rfl

/-- The cached native conversion uses the fixed target interpretation. -/
theorem EntryModel.native_target {source destination : Context registry}
    {target : Tower.Model destination R} {inclusion : Inclusion source destination}
    (model : EntryModel following reference target inclusion) :
    model.native.target = target := model.native_target_proof

/-- Reconcile the cached conversion's returned context with its declared
owner, retaining the same target interpretation. -/
noncomputable def EntryModel.inclusion {source destination : Context registry}
    {target : Tower.Model destination R} {inclusion : Inclusion source destination}
    (model : EntryModel following reference target inclusion) :
    Inclusion.Model inclusion model.original := by
  rcases inclusion with ⟨conversion, same⟩
  cases same
  exact ⟨⟨target, model.value⟩⟩

/-- Packaging a cache entry as an inclusion model retains the fixed target. -/
theorem EntryModel.inclusion_target {source destination : Context registry}
    {target : Tower.Model destination R} {inclusion : Inclusion source destination}
    (model : EntryModel following reference target inclusion) :
    model.inclusion.target = target := by
  rcases inclusion with ⟨conversion, same⟩
  cases same
  exact eq_of_heq model.inclusion.target_heq

/-- A checked base inclusion supplies the canonical original-owner model
and every source coefficient agreement directly from the provider factory. -/
noncomputable def EntryModel.ofBase (source : BaseContext.PackedContext registry)
    (following : base.Realization) (reference : Tower.Model (Context.ofBase base) R)
    (inclusion : BaseInclusion source base)
    (produced : BaseInclusion.make? source base = some inclusion) :
    EntryModel following reference reference
      ⟨Conversion.base inclusion, (Conversion.base_spec inclusion).1⟩ where
  original := (BaseInclusion.Model.derive following inclusion reference).source
  produced := Context.model?_baseMap source following reference inclusion produced
  value := by
    intro a
    have preserved := (BaseInclusion.Model.derive following inclusion reference).value a
    rw [BaseInclusion.Model.derive_target] at preserved
    exact preserved

/-- A freshly validated root map preserves the canonical child owner in
the actual target extension. Its predecessor agreement is already derived by
the incoming cache entry. -/
noncomputable def EntryModel.adjoin {source destination : Context registry}
    {target : Tower.Model destination R} {initial : Inclusion source destination}
    (model : EntryModel following reference target initial)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (converted : SignDet.Descriptor destination.Value Signature destination.sign destination.signature)
    (checked : SignDet.Descriptor.validate destination.sign destination.signature
      (source.mapDescriptor destination initial.value descriptor) = some converted) :
    EntryModel following reference (target.adjoin converted)
      ⟨initial.native.adjoinCached descriptor converted checked
        (destination.adjoin converted) rfl,
        (initial.native.adjoinCached_spec descriptor converted checked
          (destination.adjoin converted) rfl).1⟩ := by
  let result := initial.native.adjoinCached descriptor converted checked
    (destination.adjoin converted) rfl
  let spec := initial.native.adjoinCached_spec descriptor converted checked
    (destination.adjoin converted) rfl
  let binding := SignDet.Descriptor.build_raw (SignDet.Descriptor.validate_eq_some.mp checked)
  let interpreted := model.native.adjoinWith descriptor converted binding result spec.1 spec.2
  let included : Inclusion.Model ⟨result, spec.1⟩ (model.original.adjoin descriptor) :=
    ⟨interpreted⟩
  have aligned : included.target = target.adjoin converted := by
    have native := model.native.adjoinWith_target descriptor converted binding result spec.1 spec.2
    rw [model.native_target] at native
    exact eq_of_heq (included.target_heq.trans native)
  refine ⟨model.original.adjoin descriptor, ?_, ?_⟩
  · rw [Context.model?_adjoin, model.produced, Option.map_some]
  · intro a
    rw [← aligned]
    exact included.value a

/-- A checked existing generator gives the canonical child owner without
changing the fixed target model or adjoining an algebraic level. -/
noncomputable def EntryModel.reuseRoot {source destination : Context registry}
    {target : Tower.Model destination R} {initial : Inclusion source destination}
    (model : EntryModel following reference target initial)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (converted : SignDet.Descriptor destination.Value Signature destination.sign destination.signature)
    (binding : converted.raw = source.mapDescriptor destination initial.value descriptor)
    (matched : RootMatch destination converted) :
    EntryModel following reference target (initial.reuseRoot descriptor converted binding matched) := by
  let interpreted := model.native.reuseRoot descriptor converted binding matched.value matched.selected
  refine ⟨model.original.adjoin descriptor, ?_, ?_⟩
  · rw [Context.model?_adjoin, model.produced, Option.map_some]
  · intro a
    exact interpreted.value a

/-- Compose a canonical owner's interpretation through the next actual
inclusion. The source interpretation remains the same factory result. -/
noncomputable def EntryModel.comp {source destination later : Context registry}
    {target : Tower.Model destination R} {inclusion : Inclusion source destination}
    (model : EntryModel following reference target inclusion)
    (next : Inclusion destination later) (nextModel : Inclusion.Model next target) :
    EntryModel following reference nextModel.target (inclusion.comp next) where
  original := model.original
  produced := model.produced
  value := by
    intro a
    rw [Inclusion.comp_value, nextModel.value, model.value]

/-- Carry a canonical owner through one further native inclusion into the
specified target interpretation. -/
noncomputable def EntryModel.transport {source destination later : Context registry}
    {target : Tower.Model destination R} {inclusion : Inclusion source destination}
    (model : EntryModel following reference target inclusion)
    (next : Inclusion destination later) (nextTarget : Tower.Model later R)
    (preserved : ∀ a, nextTarget.value (next.value a) = target.value a) :
    EntryModel following reference nextTarget (inclusion.comp next) where
  original := model.original
  produced := model.produced
  value := by intro a; rw [Inclusion.comp_value, preserved, model.value]

/-- The empty cache has no owner maps to certify. -/
def Models.empty {destination : Context registry} (target : Tower.Model destination R) :
    Models following reference target ⟨[], []⟩ := by
  intro entry present
  exact False.elim (List.not_mem_nil present)

/-- Combine two actual caches certified in the same target interpretation. -/
noncomputable def Models.append {destination : Context registry}
    {target : Tower.Model destination R} {first second : InclusionCache destination}
    (left : Models following reference target first)
    (right : Models following reference target second) :
    Models following reference target (first.append second) := by
  intro entry present
  exact Classical.choice (by
    rcases List.mem_append.mp present with first | second
    · exact ⟨left entry first⟩
    · exact ⟨right entry second⟩)

/-- Retain the canonical owner interpretation for a newly inserted actual map. -/
noncomputable def Models.insert {destination source : Context registry}
    {target : Tower.Model destination R} {cache : InclusionCache destination}
    (models : Models following reference target cache)
    (next : Inclusion source destination)
    (model : EntryModel following reference target next) :
    Models following reference target (cache.insert next) := by
  intro entry present
  exact Classical.choice (by
    rcases List.mem_cons.mp present with same | present
    · cases same
      exact ⟨model⟩
    · exact ⟨models entry present⟩)

/-- Carry every cache entry through the same subsequent checked inclusion. -/
noncomputable def Models.extend {destination later : Context registry}
    {target : Tower.Model destination R} {cache : InclusionCache destination}
    (models : Models following reference target cache)
    (next : Inclusion destination later) (nextModel : Inclusion.Model next target) :
    Models following reference nextModel.target (cache.extend next) := by
  intro entry present
  exact Classical.choice (by
    obtain ⟨previous, stored, same⟩ := List.mem_map.mp present
    cases same
    exact ⟨(models previous stored).comp next nextModel⟩)

/-- Preserve every original cached owner under the same specified target
interpretation and the same native value inclusion. -/
noncomputable def Models.transport {destination later : Context registry}
    {target : Tower.Model destination R} {cache : InclusionCache destination}
    (models : Models following reference target cache)
    (next : Inclusion destination later) (nextTarget : Tower.Model later R)
    (preserved : ∀ a, nextTarget.value (next.value a) = target.value a) :
    Models following reference nextTarget (cache.extend next) := by
  intro entry present
  exact Classical.choice (by
    obtain ⟨previous, stored, same⟩ := List.mem_map.mp present
    cases same
    exact ⟨(models previous stored).transport next nextTarget preserved⟩)

open scoped Hex.OrderedFn.Infinitesimal in
/-- Transport one old cache entry to the constructed next base. Its original
owner interpretation is the actual next canonical factory result. -/
noncomputable def EntryModel.nextBase
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    (original : (BaseContext.PackedContext.pack base).Realization)
    (reference : Tower.Model (Context.base base) R)
    (ambient : Ambient (Hex.RationalFn R))
    {source destination later : Context registry}
    {target : Tower.Model destination R} {inclusion : Inclusion source destination}
    (model : EntryModel original reference target inclusion)
    (next : Inclusion destination later) (nextTarget : Tower.Model later ambient.Carrier)
    (preserved : ∀ a, nextTarget.value (next.value a) =
      Ambient.coefficientHom ambient (target.value a)) :
    EntryModel original.infinitesimal (Tower.Model.nextBase base reference ambient)
      nextTarget (inclusion.comp next) where
  original := model.original.map (Ambient.coefficientHom ambient)
    (Ambient.coefficientHom_strictMono ambient)
  produced := source.model?_next base original reference ambient model.original model.produced
  value := by
    intro a
    rw [Inclusion.comp_value, preserved, model.value]
    rfl

open scoped Hex.OrderedFn.Infinitesimal in
/-- Preserve the entire old predecessor cache with canonical interpretations
over the next base, through its one actual common-context inclusion. -/
noncomputable def Models.nextBase
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    (original : (BaseContext.PackedContext.pack base).Realization)
    (reference : Tower.Model (Context.base base) R)
    (ambient : Ambient (Hex.RationalFn R))
    {destination later : Context registry}
    {target : Tower.Model destination R} {cache : InclusionCache destination}
    (models : Models original reference target cache)
    (next : Inclusion destination later) (nextTarget : Tower.Model later ambient.Carrier)
    (preserved : ∀ a, nextTarget.value (next.value a) =
      Ambient.coefficientHom ambient (target.value a)) :
    Models original.infinitesimal (Tower.Model.nextBase base reference ambient)
      nextTarget (cache.extend next) := by
  intro entry present
  exact Classical.choice (by
    obtain ⟨previous, stored, same⟩ := List.mem_map.mp present
    cases same
    exact ⟨(models previous stored).nextBase base original reference ambient next nextTarget
      preserved⟩)

/-- A hit retrieves the interpretation of that exact stored owner inclusion. -/
noncomputable def Models.get {destination source : Context registry}
    {target : Tower.Model destination R} {cache : InclusionCache destination}
    (models : Models following reference target cache)
    (found : Inclusion source destination) (produced : cache.find? source = some found) :
    EntryModel following reference target found :=
  models ⟨source, found⟩ (cache.find?_mem found produced)

/-- A cached child and an incoming parent agree on every original parent
value. This follows from their factory-derived interpretations, so cache hits
need no additional coefficient agreement from the caller. -/
theorem Models.parent_agree {destination source : Context registry}
    {target : Tower.Model destination R} {cache : InclusionCache destination}
    (models : Models following reference target cache)
    (initial : Inclusion source destination)
    (incoming : EntryModel following reference target initial)
    (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)
    (found : Inclusion (source.adjoin descriptor).context destination)
    (present : cache.find? (source.adjoin descriptor).context = some found)
    (a : source.Value) :
    target.value (found.value ((source.adjoin descriptor).embed a)) =
      target.value (initial.value a) := by
  let child := models.get found present
  rw [child.value, incoming.value]
  exact source.model?_embed following reference descriptor incoming.original child.original
    incoming.produced child.produced a

end Hex.RealClosure.Tower.InclusionCache

namespace Hex.RealClosure.Tower.Suffix

variable {registry : BaseContext.Registry} {base : BaseContext.PackedContext registry}
variable {R : Type u} [Field R] [LinearOrder R] [DecidableEq R]
variable [IsStrictOrderedRing R] [IsRealClosed R]

private noncomputable def prefixes_models_proof
    (following : base.Realization) (reference : Tower.Model (Context.ofBase base) R)
    {source : Context registry} (suffix : Suffix source) :
    ∀ (model : Tower.Model source R), source.model? following reference = some model →
      InclusionCache.Models following reference (model.extend suffix) suffix.prefixes.cache := by
  induction suffix with
  | nil =>
    intro model canonical
    exact (InclusionCache.Models.empty model).insert (Inclusion.identity _)
      (InclusionCache.EntryModel.identity model canonical)
  | @root parent descriptor rest ih =>
    intro model canonical
    let child := parent.adjoin descriptor
    let first : Inclusion parent child.context :=
      ⟨Conversion.includeRoot parent descriptor child rfl,
        (Conversion.includeRoot_spec parent descriptor child rfl).1⟩
    have childCanonical : child.context.model? following reference =
        some (model.adjoin descriptor) := by
      rw [Context.model?_adjoin, canonical, Option.map_some]
    let later := ih (model.adjoin descriptor) childCanonical
    let inclusion := first.comp rest.prefixes.inclusion
    have retained : InclusionCache.EntryModel following reference
        ((model.adjoin descriptor).extend rest) inclusion :=
      ⟨model, canonical, by
        intro a
        rw [Inclusion.comp_value, rest.prefixes_value]
        have firstValue := Inclusion.value_eq
          (Conversion.includeRoot parent descriptor child rfl)
          (Conversion.includeRoot_spec parent descriptor child rfl).1 child.embed
          (Conversion.includeRoot_spec parent descriptor child rfl).2 a
        exact ((model.adjoin descriptor).extend_embed rest (first.value a)).trans
          ((congrArg (model.adjoin descriptor).value firstValue).trans
            (model.adjoin_embed descriptor a))⟩
    exact later.insert inclusion retained

/-- The actual native predecessor cache of a suffix has canonical owner
models at every retained level in its final interpretation. -/
noncomputable def prefixes_models
    (following : base.Realization) (reference : Tower.Model (Context.ofBase base) R)
    {source : Context registry} (suffix : Suffix source) (model : Tower.Model source R)
    (canonical : source.model? following reference = some model) :
    InclusionCache.Models following reference (model.extend suffix) suffix.prefixes.cache :=
  prefixes_models_proof following reference suffix model canonical

end Hex.RealClosure.Tower.Suffix

/-- info: 'Hex.RealClosure.Tower.InclusionCache.Models.parent_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.InclusionCache.Models.parent_agree

/-- info: 'Hex.RealClosure.Tower.InclusionCache.EntryModel.adjoin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.InclusionCache.EntryModel.adjoin
