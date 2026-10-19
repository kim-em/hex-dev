/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.BaseContext

public section

namespace Hex.RealClosure.BaseContext

open OrderedFn OrderedFn.Oracle

variable {registry : Registry} {K : Type} [g : Lean.Grind.Field K] [DecidableEq K]
variable {approx : K → Rat → Bounds} {nativeSign : K → Int}

/-- The real interpretation of an actual native prefix and its computed
coefficient bounds. The field dictionary retains all native operations. -/
structure RealContext.Interpretation (context : RealContext registry K approx nativeSign) where
  hom : letI : Field K := HexPolyTheory.fieldOfGrind; K →+* ℝ
  sign : ∀ a, nativeSign a = sgn (hom a)
  contains : ∀ a δ, Contains (context.approx a δ) (hom a)

/-- Exact rational coefficients start the interpretation chain. -/
@[expose] noncomputable def RealContext.Interpretation.rational (registry : Registry) :
    (RealContext.rational registry).Interpretation := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      { toFun := fun (a : Rat) => (a : ℝ)
        map_zero' := by exact Rat.cast_zero
        map_one' := by exact Rat.cast_one
        map_add' := fun a b => Rat.cast_add a b
        map_mul' := fun a b => Rat.cast_mul a b }
  · intro a
    change orderSign a = sgn (a : ℝ)
    rw [Infinitesimal.orderSign_eq]
    unfold sgn
    exact congrArg (fun (value : SignType) => (value : Int))
      (StrictMono.sign_comp (f := Rat.castHom ℝ) (Rat.cast_strictMono (K := ℝ)) a).symm
  · intro a δ
    exact ⟨le_rfl, le_rfl⟩

/-- Stored native progress proves the requested width for every actual
coefficient approximation, including prefixes reconstructed from their chains. -/
theorem RealChain.approx_width (chain : RealChain registry K approx nativeSign)
    (a : K) (δ : Rat) (positive : 0 < δ) : (approx a δ).width ≤ δ := by
  cases chain with
  | base =>
    change (δ : Rat) ≥ (a - a)
    simpa only [sub_self] using positive.le
  | step parent key bounds registered sp ap =>
    exact Real.approx_width _ a δ (ap a δ) positive

/-- Width uses the actual native prefix's stored progress at every predecessor. -/
theorem RealContext.approx_width (parent : RealContext registry K approx nativeSign)
    (a : K) (δ : Rat) (positive : 0 < δ) : (parent.approx a δ).width ≤ δ :=
  parent.chain.approx_width a δ positive

/-- Shrinking actual coefficient bounds determine one real interpretation.
Independent provider proofs therefore cannot change a prefix's values. -/
theorem RealContext.Interpretation.hom_unique
    {parent : RealContext registry K approx nativeSign}
    (left right : parent.Interpretation) : left.hom = right.hom := by
  ext a
  have widths := Real.width_tendsto (parent.approx a) (parent.approx_width a)
  exact tendsto_nhds_unique
    (Contains.endpoints_tendsto (fun n => left.contains a (Real.precision n)) widths).1
    (Contains.endpoints_tendsto (fun n => right.contains a (Real.precision n)) widths).1

/-- The coefficient part of a registered provider is supplied by the existing
prefix's actual computed bounds, rather than a new caller agreement premise. -/
theorem RealContext.Interpretation.source_correct
    {parent : RealContext registry K approx nativeSign}
    (model : parent.Interpretation) (key : ConstantKey)
    (present : (registry key).isSome = true) (τ : ℝ)
    (contained : ∀ δ, 0 < δ → Contains ((registry key).get present δ) τ) :
    letI : Field K := HexPolyTheory.fieldOfGrind
    ApproximationCorrect model.hom τ (parent.source key present) := by
  let : Field K := HexPolyTheory.fieldOfGrind
  exact ⟨fun a δ _ => model.contains a δ, contained⟩

/-- Interpret an actual registered extension through its existing search
progress. The provider supplies containment and relative transcendence at the
exact predecessor; every coefficient interpretation is derived from the parent. -/
@[expose] noncomputable def RealContext.Interpretation.constant
    {parent : RealContext registry K approx nativeSign}
    (model : parent.Interpretation) (key : ConstantKey)
    (present : (registry key).isSome = true)
    (sp : ∀ f : RationalFn K, Acc (Next (Real.attempt (parent.source key present) f)) 0)
    (ap : ∀ (f : RationalFn K) (δ : Rat),
      Acc (Next (Real.approxAttempt (parent.source key present) f (Real.requestWidth δ))) 0)
    (τ : ℝ) (contained : ∀ δ, 0 < δ → Contains ((registry key).get present δ) τ)
    (transcendental : letI : Field K := HexPolyTheory.fieldOfGrind
      Real.RelativeTranscendence model.hom τ) :
    (parent.constant key present sp ap).Interpretation := by
  letI : Field K := HexPolyTheory.fieldOfGrind
  have compatible : Field.toGrindField (K := K) = g := HexPolyTheory.toGrind_fieldOfGrind
  have correct := model.source_correct key present τ contained
  refine ⟨RealModel.evalHom compatible transcendental, ?_, ?_⟩
  · intro f
    rw [RealModel.evalHom_apply]
    exact parent.constant_sign compatible key present sp ap correct f
  · intro f δ
    rw [RealModel.evalHom_apply]
    exact parent.constant_contains compatible key present sp ap correct f δ

-- This equality identifies the two dictionaries explicitly.
set_option linter.overlappingInstances false in
/-- Evaluation of a native constant retains the predecessor embedding,
through the explicit equality of the whole coefficient-field dictionary. -/
theorem RealModel.evalHom_C [Field K] (compatible : Field.toGrindField (K := K) = g)
    {hom : K →+* ℝ} {τ : ℝ} (transcendental : Real.RelativeTranscendence hom τ) (a : K) :
    RealModel.evalHom compatible transcendental (RationalFn.C a) = hom a := by
  subst g
  change Real.evalHom transcendental (RationalFn.C a) = hom a
  exact Real.evalHom_C transcendental a

set_option linter.overlappingInstances false in
/-- The actual native generator reads as the caller's registered real value. -/
theorem RealModel.evalHom_X [Field K] (compatible : Field.toGrindField (K := K) = g)
    {hom : K →+* ℝ} {τ : ℝ} (transcendental : Real.RelativeTranscendence hom τ) :
    RealModel.evalHom compatible transcendental RationalFn.X = τ := by
  subst g
  change Real.evalHom transcendental RationalFn.X = τ
  exact Real.evalHom_X transcendental

/-- A registered interpretation preserves the actual previous coefficient
values. This identity is derived from evaluation, not supplied by a caller. -/
theorem RealContext.Interpretation.constant_embed
    {parent : RealContext registry K approx nativeSign}
    (model : parent.Interpretation) (key : ConstantKey)
    (present : (registry key).isSome = true)
    (sp : ∀ f : RationalFn K, Acc (Next (Real.attempt (parent.source key present) f)) 0)
    (ap : ∀ (f : RationalFn K) (δ : Rat),
      Acc (Next (Real.approxAttempt (parent.source key present) f (Real.requestWidth δ))) 0)
    (τ : ℝ) (contained : ∀ δ, 0 < δ → Contains ((registry key).get present δ) τ)
    (transcendental : letI : Field K := HexPolyTheory.fieldOfGrind
      Real.RelativeTranscendence model.hom τ) (a : K) :
    (model.constant key present sp ap τ contained transcendental).hom (RationalFn.C a) =
      model.hom a := by
  let : Field K := HexPolyTheory.fieldOfGrind
  change RealModel.evalHom HexPolyTheory.toGrind_fieldOfGrind transcendental
    (RationalFn.C a) = model.hom a
  exact RealModel.evalHom_C HexPolyTheory.toGrind_fieldOfGrind transcendental a

/-- Provider validity combines the parent's derived coefficient bounds with
only the registered constant's containment, width and relative transcendence. -/
theorem RealContext.Interpretation.valid
    {parent : RealContext registry K approx nativeSign}
    (model : parent.Interpretation) (key : ConstantKey)
    (present : (registry key).isSome = true) (τ : ℝ)
    (contained : ∀ δ, 0 < δ → Contains ((registry key).get present δ) τ)
    (width : ∀ δ, 0 < δ → ((registry key).get present δ).width ≤ δ)
    (transcendental : letI : Field K := HexPolyTheory.fieldOfGrind
      Real.RelativeTranscendence model.hom τ) :
    letI : Field K := HexPolyTheory.fieldOfGrind
    Real.Valid (parent.source key present) := by
  let : Field K := HexPolyTheory.fieldOfGrind
  exact ⟨model.hom, τ, model.source_correct key present τ contained,
    ⟨fun a δ positive => parent.approx_width a δ positive, width⟩, transcendental⟩

/-- Register and interpret one provider using the parent's actual model.
Progress and all coefficient agreement are derived by the existing constructors. -/
@[expose] noncomputable def RealContext.Interpretation.register
    {parent : RealContext registry K approx nativeSign}
    (model : parent.Interpretation) (key : ConstantKey)
    (present : (registry key).isSome = true) (τ : ℝ)
    (contained : ∀ δ, 0 < δ → Contains ((registry key).get present δ) τ)
    (width : ∀ δ, 0 < δ → ((registry key).get present δ).width ≤ δ)
    (transcendental : letI : Field K := HexPolyTheory.fieldOfGrind
      Real.RelativeTranscendence model.hom τ) :
    letI : Field K := HexPolyTheory.fieldOfGrind
    (RealContext.register HexPolyTheory.toGrind_fieldOfGrind parent key present
      (model.valid key present τ contained width transcendental)).Interpretation := by
  letI : Field K := HexPolyTheory.fieldOfGrind
  have compatible : Field.toGrindField (K := K) = g := HexPolyTheory.toGrind_fieldOfGrind
  let provider := model.valid key present τ contained width transcendental
  let generated := parent.registration compatible key present provider
  exact model.constant key present generated.signProgress generated.approxProgress
    τ contained transcendental

end Hex.RealClosure.BaseContext

/-- info: 'Hex.RealClosure.BaseContext.RealContext.Interpretation.constant' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealContext.Interpretation.constant

/-- info: 'Hex.RealClosure.BaseContext.RealContext.Interpretation.register' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealContext.Interpretation.register

/-- info: 'Hex.RealClosure.BaseContext.RealContext.Interpretation.constant_embed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealContext.Interpretation.constant_embed

/-- info: 'Hex.RealClosure.BaseContext.RealContext.Interpretation.hom_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.RealContext.Interpretation.hom_unique
