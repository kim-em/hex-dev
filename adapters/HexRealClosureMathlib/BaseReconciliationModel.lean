/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseOrder
public import HexRealClosureMathlib.BaseStagedReorder
public import HexRealClosureMathlib.BaseModels
public import HexRealClosureMathlib.TowerNaturality
public import HexRealClosureMathlib.TowerInclusion

public section

namespace Hex.RealClosure.BaseContext

variable {registry : Registry}

/-- Packed realizations retain the distinctness of their actual provider keys. -/
theorem PackedContext.Realization.keys_nodup {context : PackedContext registry}
    (original : context.Realization) : context.signature.constants.Nodup := by
  cases context with
  | pack context => exact Chain.Realization.keys_nodup original

/-- Both packed realizations supply distinctness for the checked native factory. -/
theorem PackedContext.Realization.reconcile_success
    {source target : PackedContext registry}
    (original : source.Realization) (following : target.Realization)
    (included : source.signature.constants ⊆ target.signature.constants)
    (depth : source.signature.infinitesimals ≤ target.signature.infinitesimals) :
    (source.reconcile? target).isSome = true :=
  source.reconcile?_success target original.keys_nodup following.keys_nodup included depth

end Hex.RealClosure.BaseContext

namespace Hex.RealClosure.Tower.BaseReconciliation

variable {registry : BaseContext.Registry} {source target : BaseContext.PackedContext registry}

/-- Both actual packed realizations guarantee success of the nominal factory. -/
theorem make?_realized (original : source.Realization) (following : target.Realization)
    (included : source.signature.constants ⊆ target.signature.constants)
    (depth : source.signature.infinitesimals ≤ target.signature.infinitesimals) :
    (BaseReconciliation.make? source target).isSome = true :=
  make?_success source target original.keys_nodup following.keys_nodup included depth

/-- The retained coefficient map preserves actual native signs of nominal values. -/
theorem sign (inclusion : BaseReconciliation source target)
    (original : source.Realization) (following : target.Realization)
    (a : (Context.ofBase source).Value) :
    (Context.ofBase target).sign (inclusion.value a) = (Context.ofBase source).sign a := by
  cases source with
  | pack source =>
    cases target with
    | pack target =>
      exact following.reconcile_sign source.chain original inclusion.coefficients inclusion.produced a.stored

/-- Nominal reconciliation preserves inherited provider values through the
actual checked map; infinitesimal values are not mapped into the ordinary reals. -/
theorem realValue (inclusion : BaseReconciliation source target)
    (original : source.Realization) (following : target.Realization)
    (a : (Context.ofBase source).Value) (r : ℝ) (inherited : original.RealValue a r) :
    following.RealValue (inclusion.value a) r := by
  cases source with
  | pack source =>
    cases target with
    | pack target =>
      exact following.reconcile_realValue source.chain original inclusion.coefficients inclusion.produced a.stored r inherited

end Hex.RealClosure.Tower.BaseReconciliation

namespace Hex.RealClosure.Tower.BaseReconciliation

variable {registry : BaseContext.Registry} {R : Type u} [Field R] [LinearOrder R]
variable {source target : BaseContext.PackedContext registry}

/-- Both actual native bases are interpreted in the same ordered field, and
their checked reconciliation preserves every original coefficient value. -/
structure Model (inclusion : BaseReconciliation source target) where
  source : Tower.Model (Context.ofBase source) R
  target : Tower.Model (Context.ofBase target) R
  value : ∀ a, target.value (inclusion.value a) = source.value a

/-- Interpret the checked coefficient map in one target model. Both chain
and packed-context factories share this value-preservation construction. -/
noncomputable def Model.ofMap
    {K S : Type} [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field S] [DecidableEq S] {sign : K → Int} {sourceSign : S → Int}
    (source : BaseContext.Context registry S sourceSign)
    (target : BaseContext.Context registry K sign)
    (inclusion : BaseReconciliation (.pack source) (.pack target))
    (targetModel : Tower.Model (Context.base target) R)
    (correct : ∀ a, sourceSign a =
      (SignType.sign ((targetModel.baseHom target).comp inclusion.coefficients.hom a) : Int)) :
    Model (R := R) inclusion := by
  letI : Field S := HexPolyMathlib.fieldOfGrind
  let f := (targetModel.baseHom target).comp inclusion.coefficients.hom
  let sourceModel := Tower.Model.base source f correct
  refine ⟨sourceModel, targetModel, ?_⟩
  intro a
  exact (targetModel.baseHom_value target (inclusion.value a)).symm.trans
    (Tower.Model.base_value source f correct a).symm

private theorem Model.ofMap_target_proof
    {K S : Type} [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field S] [DecidableEq S] {sign : K → Int} {sourceSign : S → Int}
    (source : BaseContext.Context registry S sourceSign)
    (target : BaseContext.Context registry K sign)
    (inclusion : BaseReconciliation (.pack source) (.pack target))
    (targetModel : Tower.Model (Context.base target) R)
    (correct : ∀ a, sourceSign a =
      (SignType.sign ((targetModel.baseHom target).comp inclusion.coefficients.hom a) : Int)) :
    (Model.ofMap source target inclusion targetModel correct).target = targetModel := rfl

/-- The shared coefficient factory retains the supplied target model. -/
theorem Model.ofMap_target
    {K S : Type} [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field S] [DecidableEq S] {sign : K → Int} {sourceSign : S → Int}
    (source : BaseContext.Context registry S sourceSign)
    (target : BaseContext.Context registry K sign)
    (inclusion : BaseReconciliation (.pack source) (.pack target))
    (targetModel : Tower.Model (Context.base target) R)
    (correct : ∀ a, sourceSign a =
      (SignType.sign ((targetModel.baseHom target).comp inclusion.coefficients.hom a) : Int)) :
    (Model.ofMap source target inclusion targetModel correct).target = targetModel :=
  Model.ofMap_target_proof source target inclusion targetModel correct

/-- Extract the target's actual coefficient hom and compose the checked native
map. The source model and every coefficient agreement are derived here. -/
noncomputable def Model.ofTarget
    {K S : Type} [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field S] [DecidableEq S] {sign : K → Int} {sourceSign : S → Int}
    (source : BaseContext.Chain registry S sourceSign)
    (target : BaseContext.Chain registry K sign)
    (original : source.Realization registry) (following : target.Realization registry)
    (inclusion : BaseReconciliation (.pack (BaseContext.Context.ofChain source))
      (.pack (BaseContext.Context.ofChain target)))
    (targetModel : Tower.Model (Context.base (BaseContext.Context.ofChain target)) R) :
    Model (R := R) inclusion := by
  letI : Field K := HexPolyMathlib.fieldOfGrind
  letI : Field S := HexPolyMathlib.fieldOfGrind
  let f := (targetModel.baseHom (BaseContext.Context.ofChain target)).comp inclusion.coefficients.hom
  have produced : target.reconcile? source =
      some inclusion.coefficients := by
    simpa only [BaseContext.PackedContext.reconcile?_ofChain] using inclusion.produced
  have correct : ∀ a, sourceSign a = (SignType.sign (f a) : Int) := by
    intro a
    have preserved := following.reconcile_sign source original inclusion.coefficients produced a
    exact preserved.symm.trans
      (targetModel.baseHom_sign (BaseContext.Context.ofChain target) (inclusion.coefficients.value a))
  exact Model.ofMap (BaseContext.Context.ofChain source) (BaseContext.Context.ofChain target)
    inclusion targetModel correct

/-- Construct both base interpretations in the target's derived ordered
real-closed ambient. No ambient or coefficient interpretation is supplied. -/
noncomputable def Model.ofRealizations
    {K S : Type} [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field S] [DecidableEq S] {sign : K → Int} {sourceSign : S → Int}
    (source : BaseContext.Chain registry S sourceSign)
    (target : BaseContext.Chain registry K sign)
    (original : source.Realization registry) (following : target.Realization registry)
    (inclusion : BaseReconciliation (.pack (BaseContext.Context.ofChain source))
      (.pack (BaseContext.Context.ofChain target))) :
    letI : Field K := HexPolyMathlib.fieldOfGrind
    letI := following.ordered.order
    Model (R := following.ordered.ambient.Carrier) inclusion := by
  letI : Field K := HexPolyMathlib.fieldOfGrind
  letI : LinearOrder K := following.ordered.order
  exact Model.ofTarget source target original following inclusion following.ordered.towerModel

/-- Derive source coefficients from the target model and both retained actual
provider realizations. No separate coefficient-agreement premise is supplied. -/
noncomputable def Model.derive
    (source target : BaseContext.PackedContext registry)
    (original : source.Realization) (following : target.Realization)
    (inclusion : BaseReconciliation source target)
    (targetModel : Tower.Model (Context.ofBase target) R) : Model (R := R) inclusion := by
  cases source with
  | @pack S sourceField sourceEq sourceSign source =>
    cases target with
    | @pack K targetField targetEq targetSign target =>
      letI : Field S := HexPolyMathlib.fieldOfGrind
      letI : Field K := HexPolyMathlib.fieldOfGrind
      let f := (targetModel.baseHom target).comp inclusion.coefficients.hom
      have correct : ∀ a, sourceSign a = (SignType.sign (f a) : Int) := by
        intro a
        have preserved := following.reconcile_sign source.chain original inclusion.coefficients inclusion.produced a
        exact preserved.symm.trans (targetModel.baseHom_sign target (inclusion.coefficients.value a))
      exact Model.ofMap source target inclusion targetModel correct

private theorem Model.derive_target_proof
    (source target : BaseContext.PackedContext registry)
    (original : source.Realization) (following : target.Realization)
    (inclusion : BaseReconciliation source target)
    (targetModel : Tower.Model (Context.ofBase target) R) :
    (Model.derive source target original following inclusion targetModel).target = targetModel := by
  cases source
  cases target
  simp only [Model.derive]
  exact Model.ofMap_target _ _ _ _ _

/-- Deriving original-owner coefficients retains the supplied target model. -/
theorem Model.derive_target
    (source target : BaseContext.PackedContext registry)
    (original : source.Realization) (following : target.Realization)
    (inclusion : BaseReconciliation source target)
    (targetModel : Tower.Model (Context.ofBase target) R) :
    (Model.derive source target original following inclusion targetModel).target = targetModel :=
  Model.derive_target_proof source target original following inclusion targetModel

/-- The derived common-field interpretations certify the actual native base
conversion, including its retained target and cached value map. -/
noncomputable def Model.conversion {inclusion : BaseReconciliation source target}
    (model : Model (R := R) inclusion) :
    Conversion.Model (Conversion.reconcileBase inclusion) model.source where
  target := model.target
  value := model.value

/-- The derived models also certify the fixed-owner inclusion consumed by
shared-context gathering. -/
noncomputable def Model.inclusion {inclusion : BaseReconciliation source target}
    (model : Model (R := R) inclusion) :
    Inclusion.Model
      ⟨Conversion.reconcileBase inclusion, (Conversion.reconcileBase_spec inclusion).1⟩ model.source :=
  ⟨model.conversion⟩

/-- The inclusion uses the same target interpretation as the coefficient
factory; it introduces no second choice of roots or ambient field. -/
theorem Model.inclusion_target {inclusion : BaseReconciliation source target}
    (model : Model (R := R) inclusion) : model.inclusion.target = model.target :=
  eq_of_heq model.inclusion.target_heq

end Hex.RealClosure.Tower.BaseReconciliation

/-- info: 'Hex.RealClosure.Tower.BaseReconciliation.Model.ofTarget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseReconciliation.Model.ofTarget

/-- info: 'Hex.RealClosure.Tower.BaseReconciliation.Model.inclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseReconciliation.Model.inclusion

/-- info: 'Hex.RealClosure.Tower.BaseReconciliation.Model.ofRealizations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseReconciliation.Model.ofRealizations

/-- info: 'Hex.RealClosure.Tower.BaseReconciliation.Model.ofMap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseReconciliation.Model.ofMap

/-- info: 'Hex.RealClosure.Tower.BaseReconciliation.Model.ofMap_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseReconciliation.Model.ofMap_target

/-- info: 'Hex.RealClosure.Tower.BaseReconciliation.Model.derive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseReconciliation.Model.derive

/-- info: 'Hex.RealClosure.Tower.BaseReconciliation.make?_realized' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseReconciliation.make?_realized

/-- info: 'Hex.RealClosure.Tower.BaseReconciliation.sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseReconciliation.sign

/-- info: 'Hex.RealClosure.Tower.BaseReconciliation.realValue' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseReconciliation.realValue
