/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseOrder
public import HexRealClosureMathlib.TowerNaturality
public import HexRealClosureMathlib.TowerInclusion

public section

namespace Hex.RealClosure.Tower.BaseInclusion

variable {registry : BaseContext.Registry} {R : Type u} [Field R] [LinearOrder R]
variable {source target : BaseContext.PackedContext registry}

/-- Both actual native bases are interpreted in the same ordered field, and
their checked inclusion preserves every original coefficient value. -/
structure Model (inclusion : BaseInclusion source target) where
  source : Tower.Model (Context.ofBase source) R
  target : Tower.Model (Context.ofBase target) R
  value : ∀ a, target.value (inclusion.value a) = source.value a

/-- Extract the target's actual coefficient hom and compose the checked native
map. The source model and every coefficient agreement are derived here. -/
noncomputable def Model.ofTarget
    {K S : Type} [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field S] [DecidableEq S] {sign : K → Int} {sourceSign : S → Int}
    (source : BaseContext.Chain registry S sourceSign)
    (target : BaseContext.Chain registry K sign)
    (original : source.Realization registry) (following : target.Realization registry)
    (inclusion : BaseInclusion (.pack (BaseContext.Context.ofChain source))
      (.pack (BaseContext.Context.ofChain target)))
    (targetModel : Tower.Model (Context.base (BaseContext.Context.ofChain target)) R) :
    Model (R := R) inclusion := by
  letI : Field K := HexPolyMathlib.fieldOfGrind
  letI : Field S := HexPolyMathlib.fieldOfGrind
  let f := (targetModel.baseHom (BaseContext.Context.ofChain target)).comp inclusion.coefficients.hom
  have produced : target.embedding? (.pack (BaseContext.Context.ofChain source)) =
      some inclusion.coefficients := by
    simpa only [BaseContext.PackedContext.embedding?_ofChain] using inclusion.produced
  have correct : ∀ a, sourceSign a = (SignType.sign (f a) : Int) := by
    intro a
    have preserved := following.embedding_sign source original inclusion.coefficients produced a
    exact preserved.symm.trans
      (targetModel.baseHom_sign (BaseContext.Context.ofChain target) (inclusion.coefficients.value a))
  let sourceModel := Tower.Model.base (BaseContext.Context.ofChain source) f correct
  refine ⟨sourceModel, targetModel, ?_⟩
  intro a
  exact (targetModel.baseHom_value (BaseContext.Context.ofChain target)
    (inclusion.value a)).symm.trans
    (Tower.Model.base_value (BaseContext.Context.ofChain source) f correct a).symm

/-- Construct both base interpretations in the target's derived ordered
real-closed ambient. No ambient or coefficient interpretation is supplied. -/
noncomputable def Model.ofRealizations
    {K S : Type} [Lean.Grind.Field K] [DecidableEq K]
    [Lean.Grind.Field S] [DecidableEq S] {sign : K → Int} {sourceSign : S → Int}
    (source : BaseContext.Chain registry S sourceSign)
    (target : BaseContext.Chain registry K sign)
    (original : source.Realization registry) (following : target.Realization registry)
    (inclusion : BaseInclusion (.pack (BaseContext.Context.ofChain source))
      (.pack (BaseContext.Context.ofChain target))) :
    letI : Field K := HexPolyMathlib.fieldOfGrind
    letI := following.ordered.order
    Model (R := following.ordered.ambient.Carrier) inclusion := by
  letI : Field K := HexPolyMathlib.fieldOfGrind
  letI : LinearOrder K := following.ordered.order
  exact Model.ofTarget source target original following inclusion following.ordered.towerModel

/-- The derived common-field interpretations certify the actual native base
conversion, including its retained target and cached value map. -/
noncomputable def Model.conversion {inclusion : BaseInclusion source target}
    (model : Model (R := R) inclusion) :
    Conversion.Model (Conversion.base inclusion) model.source where
  target := model.target
  value := model.value

/-- The derived models also certify the fixed-owner inclusion consumed by
shared-context gathering. -/
noncomputable def Model.inclusion {inclusion : BaseInclusion source target}
    (model : Model (R := R) inclusion) :
    Inclusion.Model
      ⟨Conversion.base inclusion, (Conversion.base_spec inclusion).1⟩ model.source :=
  ⟨model.conversion⟩

/-- The inclusion uses the same target interpretation as the coefficient
factory; it introduces no second choice of roots or ambient field. -/
theorem Model.inclusion_target {inclusion : BaseInclusion source target}
    (model : Model (R := R) inclusion) : model.inclusion.target = model.target :=
  eq_of_heq model.inclusion.target_heq

end Hex.RealClosure.Tower.BaseInclusion

/-- info: 'Hex.RealClosure.Tower.BaseInclusion.Model.ofTarget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseInclusion.Model.ofTarget

/-- info: 'Hex.RealClosure.Tower.BaseInclusion.Model.inclusion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseInclusion.Model.inclusion

/-- info: 'Hex.RealClosure.Tower.BaseInclusion.Model.ofRealizations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseInclusion.Model.ofRealizations
