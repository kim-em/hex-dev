/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.ModelEvaluation
public import HexRealClosureTheory.TowerNaturality
public import HexRealClosureTheory.StagedEvaluation
public import HexRealClosureTheory.SuffixEvaluation
public import HexRealRootsTheory.RealClosed

public section

namespace Hex.RealClosure.Tower.Model

variable {registry : BaseContext.Registry} {B K : Type}
variable [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
variable [Field K] [LinearOrder K] [DecidableEq K]

local instance : Field B := HexPolyTheory.fieldOfGrind

/-- The actual native base coefficients fill their interpreted semantic
field. No algebraic or infinitesimal generator is omitted from this map. -/
@[expose] noncomputable def baseField (base : BaseContext.Context registry B sign)
    (model : Model (Context.base base) K) :
    letI : Field B := HexPolyTheory.fieldOfGrind
    B →+* model.field := by
  letI : Field B := HexPolyTheory.fieldOfGrind
  exact {
    toFun := fun a => model.toValue (⟨a⟩ : BaseContext.Element base)
    map_zero' := Subtype.ext ((model.zero_iff 0).mpr rfl)
    map_one' := Subtype.ext model.one
    map_add' := fun a b => Subtype.ext (model.add ⟨a⟩ ⟨b⟩)
    map_mul' := fun a b => Subtype.ext (model.mul ⟨a⟩ ⟨b⟩) }

/-- Every actual semantic base value has its stored native coefficient. -/
theorem baseField_surjective (base : BaseContext.Context registry B sign)
    (model : Model (Context.base base) K) : Function.Surjective (model.baseField base) := by
  intro a
  obtain ⟨stored, equal⟩ := model.toValue_surjective a
  exact ⟨stored.stored, equal⟩

/-- Identify the base's actual semantic field with its native coefficient
field, preserving the native operations rather than supplying a new model. -/
@[expose] noncomputable def baseEquiv (base : BaseContext.Context registry B sign)
    (model : Model (Context.base base) K) :
    letI : Field B := HexPolyTheory.fieldOfGrind
    B ≃+* model.field := by
  letI : Field B := HexPolyTheory.fieldOfGrind
  exact RingEquiv.ofBijective (model.baseField base)
    ⟨(model.baseField base).injective, model.baseField_surjective base⟩

/-- The equivalence reads exactly the stored native coefficient. -/
theorem baseEquiv_symm (base : BaseContext.Context registry B sign)
    (model : Model (Context.base base) K) (a : (Context.base base).Value) :
    (model.baseEquiv base).symm (model.toValue a) = a.stored := by
  apply (model.baseEquiv base).injective
  rw [RingEquiv.apply_symm_apply]
  rfl

/-- Pull an actual native coefficient interpretation back to the semantic
base field. Both domain membership and the total reader retain their meaning. -/
noncomputable def baseInterpretation (base : BaseContext.Context registry B sign)
    (model : Model (Context.base base) K)
    (interpretation : letI : Field B := HexPolyTheory.fieldOfGrind; CoefficientMap B ℝ) :
    CoefficientMap model.field ℝ := interpretation.comap (model.baseEquiv base).symm.toRingHom

/-- Semantic-base membership is exactly native coefficient membership. -/
theorem baseInterpretation_domain (base : BaseContext.Context registry B sign)
    (model : Model (Context.base base) K)
    (interpretation : letI : Field B := HexPolyTheory.fieldOfGrind; CoefficientMap B ℝ)
    (a : (Context.base base).Value) :
    model.domain (model.baseInterpretation base interpretation) a ↔
      a.stored ∈ interpretation.domain := by
  rw [model.domain_iff, baseInterpretation, interpretation.comap_domain]
  change (model.baseEquiv base).symm (model.toValue a) ∈ interpretation.domain ↔ _
  rw [baseEquiv_symm]

/-- The semantic-base reader is the same native partial coefficient reader. -/
theorem baseInterpretation_read (base : BaseContext.Context registry B sign)
    (model : Model (Context.base base) K)
    (interpretation : letI : Field B := HexPolyTheory.fieldOfGrind; CoefficientMap B ℝ)
    (a : (Context.base base).Value) :
    model.read (model.baseInterpretation base interpretation) a = interpretation.map a.stored := by
  rw [model.read_apply, baseInterpretation, interpretation.comap_map]
  change interpretation.map ((model.baseEquiv base).symm (model.toValue a)) = _
  rw [baseEquiv_symm]

/-- Every finite native base inventory has an ordinary-real interpretation
on its actual semantic field, retaining the caller's fixed real coefficients. -/
theorem base_inventory (base : BaseContext.Context registry B sign)
    (following : base.chain.Realization registry) (model : Model (Context.base base) K)
    (values : List (Context.base base).Value) :
    ∃ interpretation : CoefficientMap model.field ℝ,
      (∀ a ∈ values, model.domain interpretation a ∧
        (SignType.sign (model.read interpretation a) : Int) = (Context.base base).sign a) ∧
      (∀ a r, following.RealValue a.stored r →
        model.domain interpretation a ∧ model.read interpretation a = r) := by
  obtain ⟨native, data, real⟩ := following.exists_interpretation (values.map (fun a => a.stored))
  refine ⟨model.baseInterpretation base native, ?_, ?_⟩
  · intro a member
    have obtained := data a.stored (List.mem_map.mpr ⟨a, member, rfl⟩)
    refine ⟨(model.baseInterpretation_domain base native a).mpr obtained.1, ?_⟩
    rw [model.baseInterpretation_read]
    exact obtained.2
  · intro a r inherited
    have old := real a.stored r inherited
    refine ⟨(model.baseInterpretation_domain base native a).mpr old.1, ?_⟩
    rw [model.baseInterpretation_read]
    exact old.2

/-- Simultaneously realize a finite family in the actual selected-root
suffix over any provider-derived real and successive-infinitesimal base.
The partial map is on the final native semantic field and retains every
caller-provided real coefficient through the actual suffix embedding. -/
theorem realize_suffix [IsStrictOrderedRing K] [IsRealClosed K]
    (base : BaseContext.Context registry B sign)
    (following : base.chain.Realization registry) (model : Model (Context.base base) K)
    (suffix : Suffix (Context.base base)) (values : List suffix.context.Value) :
    ∃ interpretation : CoefficientMap (model.extend suffix).field ℝ,
      (∀ a ∈ values, (model.extend suffix).domain interpretation a ∧
        (SignType.sign ((model.extend suffix).read interpretation a) : Int) =
          suffix.context.sign a) ∧
      (∀ a r, following.RealValue a.stored r →
        (model.extend suffix).domain interpretation (suffix.embed a) ∧
          (model.extend suffix).read interpretation (suffix.embed a) = r) := by
  obtain ⟨inventory, extend⟩ := model.extend_inventory (G := ℝ) suffix values
  obtain ⟨original, data, real⟩ := model.base_inventory base following inventory
  obtain ⟨interpretation, finite, coefficients⟩ := extend original
    (fun a member => (data a member).1) (fun a member => (data a member).2)
  refine ⟨interpretation, finite, ?_⟩
  intro a r inherited
  have old := real a r inherited
  have preserved := coefficients a old.1
  exact ⟨preserved.1, preserved.2.trans old.2⟩

end Hex.RealClosure.Tower.Model

/-- info: 'Hex.RealClosure.Tower.Model.base_inventory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.base_inventory

/-- info: 'Hex.RealClosure.Tower.Model.realize_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.realize_suffix
