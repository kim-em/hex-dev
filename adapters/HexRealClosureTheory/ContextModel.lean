/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerEnlarge
public import HexRealClosure.BaseEmbedding
public import HexRealClosureTheory.BaseFactory

public section

open scoped List

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry} {base : BaseContext.PackedContext registry}
variable {R : Type u} [Field R] [LinearOrder R] [DecidableEq R]
variable [IsStrictOrderedRing R] [IsRealClosed R]

/-- Construct an original owner's interpretation in one fixed target field.
The target base derives every compatible coefficient interpretation; the
owner's actual stored suffix supplies all selected algebraic roots. -/
noncomputable def Origin.model? {context : Context registry} (origin : Origin context)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R) :
    Option (Tower.Model context R) := by
  cases origin with
  | pack original suffix same =>
    exact (BaseInclusion.make? (.pack original) base).map fun inclusion =>
      let originalModel : Tower.Model (Context.base original) R :=
        (BaseInclusion.Model.derive (source := .pack original) (target := base)
          following inclusion target).source
      same ▸ originalModel.extend suffix

/-- Interpret a context from its actual stored origin in one target field. -/
noncomputable def Context.model? (context : Context registry)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R) :
    Option (Tower.Model context R) := context.origin.model? following target

private theorem Context.model?_origin_proof (context : Context registry)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R) :
    context.model? following target = context.origin.model? following target := rfl

/-- The canonical context factory consumes its actual stored origin. -/
theorem Context.model?_origin (context : Context registry)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R) :
    context.model? following target = context.origin.model? following target :=
  context.model?_origin_proof following target

private theorem Origin.model?_pack_proof
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (original : BaseContext.Context registry B sign) (suffix : Suffix (Context.base original))
    {context : Context registry} (same : suffix.context = context)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R) :
    (Origin.pack original suffix same).model? following target =
      ((Context.base original).model? following target).map
        (fun model => same ▸ model.extend suffix) := by
  cases same
  rw [Context.model?, Context.origin_base]
  simp only [Origin.model?]
  cases BaseInclusion.make? (.pack original) base <;> rfl

/-- A stored origin extends exactly the canonical model of its original base. -/
theorem Origin.model?_pack
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (original : BaseContext.Context registry B sign) (suffix : Suffix (Context.base original))
    {context : Context registry} (same : suffix.context = context)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R) :
    (Origin.pack original suffix same).model? following target =
      ((Context.base original).model? following target).map
        (fun model => same ▸ model.extend suffix) :=
  Origin.model?_pack_proof original suffix same following target

private theorem Context.model?_baseMap_proof
    (source : BaseContext.PackedContext registry)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R)
    (inclusion : BaseInclusion source base)
    (produced : BaseInclusion.make? source base = some inclusion) :
    (Context.ofBase source).model? following target =
      some (BaseInclusion.Model.derive following inclusion target).source := by
  cases source with
  | pack original =>
    change (Context.base original).model? following target = _
    rw [Context.model?, Context.origin_base]
    simp only [Origin.model?]
    rw [produced]
    rfl

/-- A successful coefficient inclusion supplies exactly the source model
used by the canonical owner factory at that base. -/
theorem Context.model?_baseMap
    (source : BaseContext.PackedContext registry)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R)
    (inclusion : BaseInclusion source base)
    (produced : BaseInclusion.make? source base = some inclusion) :
    (Context.ofBase source).model? following target =
      some (BaseInclusion.Model.derive following inclusion target).source :=
  Context.model?_baseMap_proof source following target inclusion produced

/-- A canonical base owner agrees with the supplied reference on every
value transported by the actual successful native coefficient inclusion. -/
theorem Context.model?_value
    (source : BaseContext.PackedContext registry)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R)
    (inclusion : BaseInclusion source base)
    (produced : BaseInclusion.make? source base = some inclusion)
    (original : Tower.Model (Context.ofBase source) R)
    (ownerProduced : (Context.ofBase source).model? following target = some original)
    (a : (Context.ofBase source).Value) :
    target.value (inclusion.value a) = original.value a := by
  have same := Context.model?_baseMap source following target inclusion produced
  rw [ownerProduced] at same
  have preserved := (BaseInclusion.Model.derive following inclusion target).value a
  rw [BaseInclusion.Model.derive_target, ← Option.some.inj same] at preserved
  exact preserved

private theorem Context.model?_base_proof
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R) :
    (Context.ofBase base).model? following target = some target := by
  cases base with
  | pack original =>
    change (Context.base original).model? following target = some target
    rw [Context.model?, Context.origin_base]
    simp only [Origin.model?]
    cases produced : BaseInclusion.make? (.pack original) (.pack original) with
    | none =>
      have success := (BaseInclusion.make?_isSome (.pack original) (.pack original)).mpr
        ⟨List.Sublist.refl _, Nat.le_refl _⟩
      rw [produced] at success
      cases success
    | some inclusion =>
      change some (BaseInclusion.Model.derive following inclusion target).source = some target
      apply congrArg some
      apply Model.value_ext
      intro a
      have preserved := (BaseInclusion.Model.derive following inclusion target).value a
      rw [BaseInclusion.Model.derive_target] at preserved
      exact preserved.symm.trans (congrArg target.value (inclusion.self_value a))

/-- At the declared target base, the owner factory returns the supplied
interpretation itself. Staged identity maps retain every native coefficient. -/
theorem Context.model?_base
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R) :
    (Context.ofBase base).model? following target = some target :=
  Context.model?_base_proof following target

private theorem Model.extend_snoc {source : Context registry} (model : Model source R)
    (suffix : Suffix source)
    (descriptor : SignDet.Descriptor suffix.context.Value Signature
      suffix.context.sign suffix.context.signature) :
    HEq (model.extend (suffix.snoc descriptor)) ((model.extend suffix).adjoin descriptor) := by
  induction suffix with
  | nil => rfl
  | root first rest ih => exact ih (model.adjoin first) descriptor

private theorem Origin.model?_snoc_proof {context : Context registry} (origin : Origin context)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature) :
    (origin.snoc descriptor).model? following target =
      (origin.model? following target).map (fun model => model.adjoin descriptor) := by
  cases origin with
  | pack original suffix same =>
    cases same
    simp only [Origin.snoc, Context.castDescriptor, Origin.model?, Option.map_map]
    congr 1
    funext inclusion
    exact eq_of_heq ((Model.cast_heq _ (Suffix.snoc_context suffix descriptor)).trans
      (Model.extend_snoc _ suffix descriptor))

/-- A canonical child owner uses the same predecessor model and its actual
selected descriptor. This agreement is derived from the stored origin. -/
theorem Context.model?_adjoin (context : Context registry)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature) :
    (context.adjoin descriptor).context.model? following target =
      (context.model? following target).map (fun model => model.adjoin descriptor) := by
  simp only [Context.model?, Context.origin_adjoin]
  exact context.origin.model?_snoc_proof following target descriptor

/-- The constructed child interpretation preserves its original parent's
values. No agreement hypothesis is supplied beyond the two factory results. -/
theorem Context.model?_embed (context : Context registry)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R)
    (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature)
    (original : Tower.Model context R)
    (child : Tower.Model (context.adjoin descriptor).context R)
    (parentProduced : context.model? following target = some original)
    (childProduced : (context.adjoin descriptor).context.model? following target = some child)
    (a : context.Value) :
    child.value ((context.adjoin descriptor).embed a) = original.value a := by
  have same := context.model?_adjoin following target descriptor
  rw [parentProduced, childProduced, Option.map_some] at same
  rw [Option.some.inj same, original.adjoin_embed descriptor a]

/-- Canonical interpretation of every actual selected-root suffix extends the
canonical model of its starting context. -/
theorem Suffix.model?_extend {source : Context registry} (suffix : Suffix source)
    (following : base.Realization) (reference : Tower.Model (Context.ofBase base) R) :
    ∀ (model : Tower.Model source R), source.model? following reference = some model →
      suffix.context.model? following reference = some (model.extend suffix) := by
  induction suffix with
  | nil => intro model canonical; exact canonical
  | root descriptor rest ih =>
    intro model canonical
    exact ih (model.adjoin descriptor) (by
      rw [Context.model?_adjoin, canonical, Option.map_some])

private theorem Context.model?_isSome_proof (context : Context registry)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R) :
    (context.model? following target).isSome = true ↔
      List.Sublist context.origin.base.signature.constants base.signature.constants ∧
        context.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals := by
  have packaged : (context.model? following target).isSome =
      (BaseInclusion.make? context.origin.base base).isSome := by
    simp only [Context.model?, Origin.model?, Origin.base, Option.isSome_map]
  rw [packaged]
  exact BaseInclusion.make?_isSome context.origin.base base

/-- Every owner over a compatible actual staged base obtains a model in the
same target field; unrelated paths and decreasing depth are rejected. -/
theorem Context.model?_isSome (context : Context registry)
    (following : base.Realization) (target : Tower.Model (Context.ofBase base) R) :
    (context.model? following target).isSome = true ↔
      List.Sublist context.origin.base.signature.constants base.signature.constants ∧
        context.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals :=
  context.model?_isSome_proof following target

private theorem Origin.model?_next_proof
    {context : Context registry}
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    {S : Type v} [Field S] [LinearOrder S] [DecidableEq S]
    [IsStrictOrderedRing S] [IsRealClosed S]
    (origin : Origin context) (base : BaseContext.Context registry B sign)
    (original : (BaseContext.PackedContext.pack base).Realization)
    (following : (BaseContext.PackedContext.pack base.infinitesimal).Realization)
    (oldBase : Tower.Model (Context.ofBase (.pack base)) R)
    (nextBase : Tower.Model (Context.ofBase (.pack base.infinitesimal)) S)
    (embedding : R →+* S) (ordered : StrictMono embedding)
    (constants : ∀ a, nextBase.value (BaseContext.Element.embed a) =
      embedding (oldBase.value a))
    (old : Tower.Model context R) (next : Tower.Model context S)
    (oldProduced : origin.model? original oldBase = some old)
    (nextProduced : origin.model? following nextBase = some next)
    (a : context.Value) : next.value a = embedding (old.value a) := by
  cases origin with
  | pack source suffix same =>
    cases same
    cases first : BaseInclusion.make? (.pack source) (.pack base) with
    | none => simp [Origin.model?, first] at oldProduced
    | some oldInclusion =>
      cases second : BaseInclusion.make? (.pack source) (.pack base.infinitesimal) with
      | none => simp [Origin.model?, second] at nextProduced
      | some nextInclusion =>
        simp only [Origin.model?, first, Option.map_some] at oldProduced
        simp only [Origin.model?, second, Option.map_some] at nextProduced
        have oldEq : (BaseInclusion.Model.derive original oldInclusion oldBase).source.extend
            suffix = old := Option.some.inj oldProduced
        have nextEq : (BaseInclusion.Model.derive following nextInclusion nextBase).source.extend
            suffix = next := Option.some.inj nextProduced
        rw [← oldEq, ← nextEq]
        rw [BaseInclusion.Model.derive_next base oldInclusion nextInclusion original following
          oldBase nextBase embedding ordered constants]
        exact Tower.Model.map_extend _ embedding ordered suffix a

/-- The canonical owner factory commutes with the next base inclusion through
every stored selected root. Only the actual two factory results are compared. -/
theorem Origin.model?_next
    {context : Context registry}
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    {S : Type v} [Field S] [LinearOrder S] [DecidableEq S]
    [IsStrictOrderedRing S] [IsRealClosed S]
    (origin : Origin context) (base : BaseContext.Context registry B sign)
    (original : (BaseContext.PackedContext.pack base).Realization)
    (following : (BaseContext.PackedContext.pack base.infinitesimal).Realization)
    (oldBase : Tower.Model (Context.ofBase (.pack base)) R)
    (nextBase : Tower.Model (Context.ofBase (.pack base.infinitesimal)) S)
    (embedding : R →+* S) (ordered : StrictMono embedding)
    (constants : ∀ a, nextBase.value (BaseContext.Element.embed a) =
      embedding (oldBase.value a))
    (old : Tower.Model context R) (next : Tower.Model context S)
    (oldProduced : origin.model? original oldBase = some old)
    (nextProduced : origin.model? following nextBase = some next)
    (a : context.Value) : next.value a = embedding (old.value a) :=
  origin.model?_next_proof base original following oldBase nextBase embedding ordered
    constants old next oldProduced nextProduced a

open scoped Hex.OrderedFn.Infinitesimal in
/-- Canonical owner models in the constructed enlarged base are exactly the
ordered images of the old canonical models. Provider history and constant
agreement are both derived, including every stored algebraic root. -/
theorem Context.model?_next_eq (context : Context registry)
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    (original : (BaseContext.PackedContext.pack base).Realization)
    (reference : Tower.Model (Context.base base) R)
    (ambient : Ambient (Hex.RationalFn R))
    (old : Tower.Model context R) (next : Tower.Model context ambient.Carrier)
    (oldProduced : context.model? original reference = some old)
    (nextProduced : context.model? original.infinitesimal
      (Tower.Model.nextBase base reference ambient) = some next) :
    next = old.map (Ambient.coefficientHom ambient)
      (Ambient.coefficientHom_strictMono ambient) := by
  apply Tower.Model.value_ext
  intro a
  exact context.origin.model?_next base original original.infinitesimal reference
    (Tower.Model.nextBase base reference ambient) (Ambient.coefficientHom ambient)
    (Ambient.coefficientHom_strictMono ambient)
    (Tower.Model.nextBase_embed base reference ambient) old next oldProduced nextProduced a

open scoped Hex.OrderedFn.Infinitesimal in
/-- Every old canonical owner is accepted by the next base's factory, which
returns its ordered image without an additional interpretation premise. -/
theorem Context.model?_next (context : Context registry)
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    (original : (BaseContext.PackedContext.pack base).Realization)
    (reference : Tower.Model (Context.base base) R)
    (ambient : Ambient (Hex.RationalFn R))
    (old : Tower.Model context R)
    (oldProduced : context.model? original reference = some old) :
    context.model? original.infinitesimal (Tower.Model.nextBase base reference ambient) =
      some (old.map (Ambient.coefficientHom ambient)
        (Ambient.coefficientHom_strictMono ambient)) := by
  have compatible := (context.model?_isSome original reference).mp (by rw [oldProduced]; rfl)
  have success := (context.model?_isSome original.infinitesimal
    (Tower.Model.nextBase base reference ambient)).mpr (by
      change context.origin.base.signature.constants <+
          ((BaseContext.PackedContext.pack base).infinitesimal).signature.constants ∧
        context.origin.base.signature.infinitesimals ≤
          ((BaseContext.PackedContext.pack base).infinitesimal).signature.infinitesimals
      rw [BaseContext.PackedContext.infinitesimal_signature]
      exact ⟨compatible.1, Nat.le.step compatible.2⟩)
  cases produced : context.model? original.infinitesimal
      (Tower.Model.nextBase base reference ambient) with
  | none => rw [produced] at success; cases success
  | some next =>
    exact congrArg some
      (context.model?_next_eq base original reference ambient old next oldProduced produced)

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Context.model?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.model?

/-- info: 'Hex.RealClosure.Tower.Context.model?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.model?_isSome

/-- info: 'Hex.RealClosure.Tower.Context.model?_adjoin' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.model?_adjoin

/-- info: 'Hex.RealClosure.Tower.Context.model?_embed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.model?_embed

/-- info: 'Hex.RealClosure.Tower.Context.model?_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.model?_value

/-- info: 'Hex.RealClosure.Tower.Context.model?_base' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.model?_base

/-- info: 'Hex.RealClosure.Tower.Context.model?_baseMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Context.model?_baseMap
