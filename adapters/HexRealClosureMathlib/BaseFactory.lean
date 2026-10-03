/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseModels
public import HexRealClosureMathlib.BaseMapModel

public section

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
      let sourceModel := Tower.Model.base source f correct
      refine ⟨sourceModel, targetModel, ?_⟩
      intro a
      exact (targetModel.baseHom_value target (inclusion.value a)).symm.trans
        (Tower.Model.base_value source f correct a).symm

private theorem Model.derive_target_proof
    {source target : BaseContext.PackedContext registry}
    (following : target.Realization) (inclusion : BaseInclusion source target)
    (targetModel : Tower.Model (Context.ofBase target) R) :
    (Model.derive following inclusion targetModel).target = targetModel := by
  cases source
  cases target
  rfl

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
