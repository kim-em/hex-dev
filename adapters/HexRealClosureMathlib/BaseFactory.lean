/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseModels
public import HexRealClosureMathlib.BaseMapModel
public import HexRealClosure.BaseEmbedding
public import HexRealClosure.TowerEnlarge

public section

namespace Hex.RealClosure.BaseContext

/-- An ordered real-closed reference field and interpretation for one packed
native base. Its field is constructed from the base's actual realization. -/
structure PackedContext.Reference {registry : Registry} (base : PackedContext registry) where
  Carrier : Type
  field : Field Carrier
  order : LinearOrder Carrier
  ordered : letI := field; letI := order; IsStrictOrderedRing Carrier
  closed : letI := field; IsRealClosed Carrier
  model : letI := field; letI := order; Tower.Model (Tower.Context.ofBase base) Carrier
  inclusion : base.Carrier → Carrier
  value : ∀ a, model.value a = inclusion (Tower.Context.baseStored base a)

instance {registry : Registry} {base : PackedContext registry} (reference : base.Reference) :
    Field reference.Carrier := reference.field
instance {registry : Registry} {base : PackedContext registry} (reference : base.Reference) :
    LinearOrder reference.Carrier := reference.order
instance {registry : Registry} {base : PackedContext registry} (reference : base.Reference) :
    IsStrictOrderedRing reference.Carrier := reference.ordered
instance {registry : Registry} {base : PackedContext registry} (reference : base.Reference) :
    IsRealClosed reference.Carrier := reference.closed

/-- Construct the reference directly from the actual staged realization and
ordered real-closure existence theorem, with no supplied ambient field. -/
noncomputable def PackedContext.Realization.reference {registry : Registry}
    {base : PackedContext registry} (following : base.Realization) : base.Reference := by
  classical
  cases base with
  | @pack K field equality sign context =>
    letI : Field K := HexPolyMathlib.fieldOfGrind
    let ordered := following.ordered
    letI : LinearOrder K := ordered.order
    let ambient := ordered.ambient
    have correct : ∀ a, sign a = (SignType.sign (ambient.inclusion a) : Int) := by
      intro a
      exact (ordered.sign a).trans (congrArg (fun s : SignType => (s : Int))
        (ambient.monotone.sign_comp a).symm)
    let model := Tower.Model.base context ambient.inclusion correct
    refine ⟨ambient.Carrier, inferInstance, inferInstance,
      inferInstance, inferInstance, model, ambient.inclusion, ?_⟩
    intro a
    exact Tower.Model.base_value context ambient.inclusion correct a

end Hex.RealClosure.BaseContext

namespace Hex.RealClosure.Tower.BaseInclusion

variable {registry : BaseContext.Registry} {R : Type u} [Field R] [LinearOrder R]

/-- Construct models for the actual nominal base handles. The checked map
and the target's provider history derive every source premise and coefficient
agreement, without unpacking contexts at the call site. -/
noncomputable def Model.derive
    {source target : BaseContext.PackedContext registry}
    (following : target.Realization) (inclusion : BaseInclusion source target)
    (targetModel : Tower.Model (Context.ofBase target) R) : Model (R := R) inclusion := by
  cases source with
  | @pack S sourceField sourceEq sourceSign source =>
    cases target with
    | @pack K targetField targetEq targetSign target =>
      letI : Field S := HexPolyMathlib.fieldOfGrind
      letI : Field K := HexPolyMathlib.fieldOfGrind
      have compatible := (BaseContext.PackedContext.subsequence?_isSome
        (.pack source) (.pack target)).mp (by rw [inclusion.produced]; rfl)
      have success := (following.restrict?_isSome (.pack source)).mpr compatible
      have original : source.chain.Realization registry :=
        (following.restrict? (.pack source)).get success
      have produced : target.chain.subsequence? source.chain = some inclusion.coefficients :=
        inclusion.produced
      let f := (targetModel.baseHom target).comp inclusion.coefficients.hom
      have correct : ∀ a, sourceSign a = (SignType.sign (f a) : Int) := by
        intro a
        have preserved := BaseContext.Chain.Realization.subsequence_sign following source.chain
          original inclusion.coefficients produced a
        exact preserved.symm.trans (targetModel.baseHom_sign target (inclusion.coefficients.value a))
      exact Model.ofMap source target inclusion targetModel correct

private theorem Model.derive_target_proof
    {source target : BaseContext.PackedContext registry}
    (following : target.Realization) (inclusion : BaseInclusion source target)
    (targetModel : Tower.Model (Context.ofBase target) R) :
    (Model.derive following inclusion targetModel).target = targetModel := by
  cases source
  cases target
  simp only [Model.derive]
  exact Model.ofMap_target _ _ _ _ _

/-- The source factory retains the supplied target interpretation itself. -/
theorem Model.derive_target
    {source target : BaseContext.PackedContext registry}
    (following : target.Realization) (inclusion : BaseInclusion source target)
    (targetModel : Tower.Model (Context.ofBase target) R) :
    (Model.derive following inclusion targetModel).target = targetModel :=
  Model.derive_target_proof following inclusion targetModel

/-- Deriving a source model commutes with the checked inclusion into the next
infinitesimal base whenever the actual target models preserve its constants. -/
theorem Model.derive_next_value
    {source : BaseContext.PackedContext registry}
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    {S : Type v} [Field S] [LinearOrder S]
    (target : BaseContext.Context registry B sign)
    (old : BaseInclusion source (.pack target))
    (next : BaseInclusion source (.pack target.infinitesimal))
    (original : (BaseContext.PackedContext.pack target).Realization)
    (following : (BaseContext.PackedContext.pack target.infinitesimal).Realization)
    (oldModel : Tower.Model (Context.ofBase (.pack target)) R)
    (nextModel : Tower.Model (Context.ofBase (.pack target.infinitesimal)) S)
    (embedding : R →+* S)
    (constants : ∀ a, nextModel.value (BaseContext.Element.embed a) =
      embedding (oldModel.value a))
    (a : (Context.ofBase source).Value) :
    (Model.derive following next nextModel).source.value a =
      embedding ((Model.derive original old oldModel).source.value a) := by
  rw [← (Model.derive following next nextModel).value,
    Model.derive_target, BaseInclusion.next_value target old next]
  have preserved := (Model.derive original old oldModel).value a
  rw [Model.derive_target] at preserved
  exact (constants (old.value a)).trans (congrArg embedding preserved)

/-- The source interpretation itself is transported through the ordered
ambient embedding; no separate choice of a source model remains. -/
theorem Model.derive_next
    {source : BaseContext.PackedContext registry}
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    {S : Type v} [Field S] [LinearOrder S]
    (target : BaseContext.Context registry B sign)
    (old : BaseInclusion source (.pack target))
    (next : BaseInclusion source (.pack target.infinitesimal))
    (original : (BaseContext.PackedContext.pack target).Realization)
    (following : (BaseContext.PackedContext.pack target.infinitesimal).Realization)
    (oldModel : Tower.Model (Context.ofBase (.pack target)) R)
    (nextModel : Tower.Model (Context.ofBase (.pack target.infinitesimal)) S)
    (embedding : R →+* S) (ordered : StrictMono embedding)
    (constants : ∀ a, nextModel.value (BaseContext.Element.embed a) =
      embedding (oldModel.value a)) :
    (Model.derive following next nextModel).source =
      (Model.derive original old oldModel).source.map embedding ordered := by
  apply Tower.Model.value_ext
  intro a
  exact Model.derive_next_value target old next original following oldModel nextModel
    embedding constants a

end Hex.RealClosure.Tower.BaseInclusion

namespace Hex.RealClosure.Tower.Model

open scoped Hex.OrderedFn.Infinitesimal

variable {registry : BaseContext.Registry} {R : Type u}
variable [Field R] [LinearOrder R] [DecidableEq R] [IsStrictOrderedRing R]

/-- Construct the new native base interpretation from the old model's actual
coefficient hom in an ordered algebraic ambient over its rational functions. -/
noncomputable def nextBase {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    (old : Model (Context.base base) R) (ambient : Ambient (Hex.RationalFn R)) :
    Model (Context.base base.infinitesimal) ambient.Carrier :=
  (Conversion.infinitesimal_spec base).1 ▸
    (Conversion.Model.infinitesimalMapped base (old.baseHom base)
      (old.baseHom_sign base) ambient).target

private theorem cast_value {source target : Context registry}
    {K : Type v} [Field K] [LinearOrder K] (same : source = target)
    (model : Model source K) (a : source.Value) :
    (same ▸ model).value (_root_.cast (congrArg Context.Value same) a) = model.value a := by
  cases same
  rfl

private theorem nextBase_embed_proof {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    (old : Model (Context.base base) R) (ambient : Ambient (Hex.RationalFn R))
    (a : (Context.base base).Value) :
    (nextBase base old ambient).value (BaseContext.Element.embed a) =
      Ambient.coefficientHom ambient (old.value a) := by
  letI : Field B := HexPolyMathlib.fieldOfGrind
  let input := Conversion.Model.infinitesimalMapped base (old.baseHom base)
    (old.baseHom_sign base) ambient
  have aligned := cast_value (Conversion.infinitesimal_spec base).1 input.target
    ((Conversion.infinitesimal base).value a)
  have included := congrArg (nextBase base old ambient).value
    (Conversion.infinitesimal_value base a)
  have coefficient := Model.base_value base
    ((Ambient.coefficientHom ambient).comp (old.baseHom base))
    (Conversion.Model.mapped_base_sign (old.baseHom base) (old.baseHom_sign base) ambient) a
  exact included.symm.trans (aligned.trans ((input.value a).trans
    (coefficient.trans (congrArg (Ambient.coefficientHom ambient) (old.baseHom_value base a)))))

/-- Constants preserve the old interpretation in the constructed new base.
This agreement is a conclusion of the factory, rather than a caller premise. -/
theorem nextBase_embed {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    (old : Model (Context.base base) R) (ambient : Ambient (Hex.RationalFn R))
    (a : (Context.base base).Value) :
    (nextBase base old ambient).value (BaseContext.Element.embed a) =
      Ambient.coefficientHom ambient (old.value a) := nextBase_embed_proof base old ambient a

private theorem nextBase_target_proof {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    (old : Model (Context.base base) R) (ambient : Ambient (Hex.RationalFn R)) :
    HEq (Conversion.Model.infinitesimalMapped base (old.baseHom base)
      (old.baseHom_sign base) ambient).target (nextBase base old ambient) := by
  exact ((Conversion.Model.infinitesimalMapped base (old.baseHom base)
    (old.baseHom_sign base) ambient).target.cast_heq (Conversion.infinitesimal_spec base).1).symm

/-- The constructed next base is the actual infinitesimal conversion's target,
with only its native context ownership aligned. -/
theorem nextBase_target {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    (old : Model (Context.base base) R) (ambient : Ambient (Hex.RationalFn R)) :
    HEq (Conversion.Model.infinitesimalMapped base (old.baseHom base)
      (old.baseHom_sign base) ambient).target (nextBase base old ambient) :=
  nextBase_target_proof base old ambient

private theorem nextBase_parameter_proof {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    (old : Model (Context.base base) R) (ambient : Ambient (Hex.RationalFn R)) :
    (nextBase base old ambient).value (BaseContext.Element.infinitesimal base) =
      ambient.inclusion (Hex.RationalFn.X : Hex.RationalFn R) := by
  let input := Conversion.Model.infinitesimalMapped base (old.baseHom base)
    (old.baseHom_sign base) ambient
  have aligned := cast_value (Conversion.infinitesimal_spec base).1 input.target
    (Conversion.parameter base)
  have owned : _root_.cast (congrArg Context.Value (Conversion.infinitesimal_spec base).1)
      (Conversion.parameter base) = BaseContext.Element.infinitesimal base := by
    unfold Conversion.parameter
    exact eq_of_heq ((_root_.cast_heq _ _).trans (_root_.cast_heq _ _))
  rw [owned] at aligned
  exact aligned.trans (Conversion.Model.infinitesimalMapped_X base (old.baseHom base)
    (old.baseHom_sign base) ambient)

/-- The newly constructed base's native parameter denotes the actual
infinitesimal in the prescribed ambient. -/
theorem nextBase_parameter {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    (old : Model (Context.base base) R) (ambient : Ambient (Hex.RationalFn R)) :
    (nextBase base old ambient).value (BaseContext.Element.infinitesimal base) =
      ambient.inclusion (Hex.RationalFn.X : Hex.RationalFn R) :=
  nextBase_parameter_proof base old ambient

/-- Construct the next interpretation directly from an immutable packed base. -/
noncomputable def next (base : BaseContext.PackedContext registry)
    (old : Model (Context.ofBase base) R) (ambient : Ambient (Hex.RationalFn R)) :
    Model (Context.ofBase base.infinitesimal) ambient.Carrier := by
  cases base with
  | pack base => exact nextBase base old ambient

private theorem next_pack_proof {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    (old : Model (Context.base base) R) (ambient : Ambient (Hex.RationalFn R)) :
    next (.pack base) old ambient = nextBase base old ambient := rfl

/-- Unpacking a base retains the same constructed interpretation. -/
theorem next_pack {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    (old : Model (Context.base base) R) (ambient : Ambient (Hex.RationalFn R)) :
    next (.pack base) old ambient = nextBase base old ambient := next_pack_proof base old ambient

end Hex.RealClosure.Tower.Model

/-- info: 'Hex.RealClosure.Tower.BaseInclusion.Model.derive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseInclusion.Model.derive

/-- info: 'Hex.RealClosure.Tower.BaseInclusion.Model.derive_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseInclusion.Model.derive_target

/-- info: 'Hex.RealClosure.BaseContext.PackedContext.Realization.reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.PackedContext.Realization.reference

/-- info: 'Hex.RealClosure.Tower.Model.nextBase_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.nextBase_parameter
