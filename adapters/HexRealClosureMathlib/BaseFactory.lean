/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseModels
public import HexRealClosureMathlib.BaseMapModel

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
      have compatible := (BaseContext.PackedContext.embedding?_isSome
        (.pack source) (.pack target)).mp (by rw [inclusion.produced]; rfl)
      have success := (following.restrict?_isSome (.pack source)).mpr compatible
      have original : source.chain.Realization registry :=
        (following.restrict? (.pack source)).get success
      let coefficients : BaseContext.FieldEmbedding S K := inclusion.coefficients
      have produced : target.chain.embedding? (.pack (BaseContext.Context.ofChain source.chain)) =
          some inclusion.coefficients := by
        change target.chain.embedding? (.pack (BaseContext.Context.ofChain source.chain)) =
          some coefficients
        rw [BaseContext.Context.ofChain_eq source]
        have checked : (BaseContext.PackedContext.pack source).embedding? (.pack target) =
            some coefficients := inclusion.produced
        rw [← BaseContext.Context.ofChain_eq target] at checked
        rw [BaseContext.PackedContext.embedding?_ofChain] at checked
        exact checked
      let f := (targetModel.baseHom target).comp inclusion.coefficients.hom
      have correct : ∀ a, sourceSign a = (SignType.sign (f a) : Int) := by
        intro a
        have preserved := BaseContext.Chain.Realization.embedding_sign following source.chain
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

end Hex.RealClosure.Tower.BaseInclusion

/-- info: 'Hex.RealClosure.Tower.BaseInclusion.Model.derive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseInclusion.Model.derive

/-- info: 'Hex.RealClosure.Tower.BaseInclusion.Model.derive_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseInclusion.Model.derive_target

/-- info: 'Hex.RealClosure.BaseContext.PackedContext.Realization.reference' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.PackedContext.Realization.reference
