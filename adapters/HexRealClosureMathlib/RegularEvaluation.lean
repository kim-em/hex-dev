/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.RingTheory.Localization.Basic
public import HexRealClosureMathlib.CoefficientMap

public section

namespace Hex.RealClosure.Specialize.Regular

variable {F G : Type*} [Field F] [Field G]

/-- Exactly the denominators surviving the coefficient interpretation. -/
def denominators {domain : Subring F} (value : domain →+* G) : Submonoid domain where
  carrier := {a | value a ≠ 0}
  one_mem' := by simp
  mul_mem' := by
    intro a b ha hb
    change value (a * b) ≠ 0
    simpa only [map_mul] using mul_ne_zero ha hb

private theorem source_units (domain : Subring F) (value : domain →+* G)
    (a : denominators value) : IsUnit (domain.subtype a) := by
  apply isUnit_iff_ne_zero.mpr
  intro zero
  have sourceZero : (a : domain) = 0 := Subtype.ext zero
  exact a.property (by rw [sourceZero, map_zero])

/-- Fractions with surviving denominators embed in the original field. -/
noncomputable def source (domain : Subring F) (value : domain →+* G) :
    Localization (denominators value) →+* F :=
  IsLocalization.lift (source_units domain value)

theorem source_injective (domain : Subring F) (value : domain →+* G) :
    Function.Injective (source domain value) := by
  apply (IsLocalization.lift_injective_iff (source_units domain value)).mpr
  intro a b
  have regular : denominators value ≤ nonZeroDivisors domain := by
    intro d hd
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    intro zero
    exact hd (by rw [zero, map_zero])
  constructor
  · intro equal
    exact congrArg domain.subtype (IsLocalization.injective _ regular equal)
  · intro equal
    exact congrArg (algebraMap domain (Localization (denominators value))) (Subtype.ext equal)

/-- The same localization evaluates in the target because every inverted
denominator is nonzero there. The map need not be injective. -/
noncomputable def target {domain : Subring F} (value : domain →+* G) :
    Localization (denominators value) →+* G :=
  IsLocalization.lift (fun a : denominators value => isUnit_iff_ne_zero.mpr a.property)

/-- Evaluation on the actual source-field image is independent of the
fraction presentation, using the injectivity of its source embedding. -/
noncomputable def evaluation (domain : Subring F) (value : domain →+* G) :
    (source domain value).range →+* G :=
  (source domain value).rangeRestrict.liftOfSurjective
    (source domain value).rangeRestrict_surjective
    ⟨target value, by
      intro a zero
      apply RingHom.mem_ker.mpr
      have sourceZero : source domain value a = source domain value 0 := by
        have equal := congrArg Subtype.val (RingHom.mem_ker.mp zero)
        change source domain value a = 0 at equal
        simpa only [map_zero] using equal
      rw [source_injective domain value sourceZero, map_zero]⟩

theorem evaluation_apply (domain : Subring F) (value : domain →+* G)
    (a : Localization (denominators value)) :
    evaluation domain value ((source domain value).rangeRestrict a) = target value a := by
  exact RingHom.liftOfSurjective_comp_apply _ _ _ _

/-- Original interpreted coefficients retain their values after adjoining
all fractions whose denominators survive. -/
theorem evaluation_coefficient (domain : Subring F) (value : domain →+* G) (a : domain) :
    evaluation domain value ((source domain value).rangeRestrict
      (algebraMap domain (Localization (denominators value)) a)) = value a := by
  rw [evaluation_apply]
  exact IsLocalization.lift_eq _ _

/-- Every regular fraction is evaluated as its numerator divided by the
surviving denominator. -/
theorem evaluation_fraction (domain : Subring F) (value : domain →+* G)
    (a : domain) (b : denominators value) :
    evaluation domain value ((source domain value).rangeRestrict
      (IsLocalization.mk' (Localization (denominators value)) a b)) = value a / value b := by
  rw [evaluation_apply]
  exact (IsLocalization.lift_mk'_spec
    (fun c : denominators value => isUnit_iff_ne_zero.mpr c.property)
    a (value a / value b) b).mpr (by rw [mul_comm, div_mul_cancel₀ _ b.property])

/-- A regular fraction with nonzero evaluated value has its inverse in the
same source-field image. The numerator becomes another surviving denominator. -/
theorem inv_mem (domain : Subring F) (value : domain →+* G)
    (a : (source domain value).range) (nonzero : evaluation domain value a ≠ 0) :
    (a : F)⁻¹ ∈ (source domain value).range := by
  obtain ⟨z, original⟩ := a.property
  obtain ⟨numerator, denominator, rfl⟩ :=
    IsLocalization.exists_mk'_eq (denominators value) z
  have same : a = (source domain value).rangeRestrict
      (IsLocalization.mk' (Localization (denominators value)) numerator denominator) :=
    Subtype.ext original.symm
  have evaluated := evaluation_fraction domain value numerator denominator
  rw [← same] at evaluated
  have survives : value numerator ≠ 0 := by
    intro zero
    rw [zero, zero_div] at evaluated
    exact nonzero evaluated
  have eligible : numerator ∈ denominators value := by
    change value numerator ≠ 0
    exact survives
  let next := IsLocalization.mk' (Localization (denominators value))
    (denominator : domain) (⟨numerator, eligible⟩ : denominators value)
  have product : (a : F) * source domain value next = 1 := by
    dsimp only [next]
    rw [← original, ← map_mul,
      IsLocalization.mk'_mul_mk'_eq_one' (S := Localization (denominators value)) numerator denominator eligible,
      map_one]
  have sourceNonzero : (a : F) ≠ 0 := by
    intro zero
    rw [zero, zero_mul] at product
    exact zero_ne_one product
  refine ⟨next, ?_⟩
  apply mul_left_cancel₀ sourceNonzero
  rw [product, mul_inv_cancel₀ sourceNonzero]

/-- info: 'Hex.RealClosure.Specialize.Regular.evaluation_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Specialize.Regular.evaluation_apply

end Hex.RealClosure.Specialize.Regular

namespace Hex.RealClosure.CoefficientMap

variable {F G : Type} [Field F] [Field G]

/-- Enlarge the interpretation domain by fractions with surviving denominators. -/
noncomputable def regular (interpretation : CoefficientMap F G) : CoefficientMap F G where
  domain := (Specialize.Regular.source interpretation.domain interpretation.value).range
  value := Specialize.Regular.evaluation interpretation.domain interpretation.value

/-- Regular fractions include every previously interpreted coefficient. -/
theorem regular_mem (interpretation : CoefficientMap F G) (a : F)
    (mem : a ∈ interpretation.domain) : a ∈ interpretation.regular.domain := by
  refine ⟨algebraMap interpretation.domain
    (Localization (Specialize.Regular.denominators interpretation.value)) ⟨a, mem⟩, ?_⟩
  exact IsLocalization.lift_eq _ _

/-- Enlarging by regular fractions preserves the existing interpretation. -/
theorem regular_map [DecidableEq F] [DecidableEq G] (interpretation : CoefficientMap F G) (a : F)
    (mem : a ∈ interpretation.domain) : interpretation.regular.map a = interpretation.map a := by
  rw [map_mem _ _ (regular_mem interpretation a mem), map_mem _ _ mem]
  let z := algebraMap interpretation.domain
    (Localization (Specialize.Regular.denominators interpretation.value)) ⟨a, mem⟩
  have bound : (Specialize.Regular.source interpretation.domain interpretation.value).rangeRestrict z =
      (⟨a, regular_mem interpretation a mem⟩ : interpretation.regular.domain) := by
    apply Subtype.ext
    exact IsLocalization.lift_eq _ _
  change Specialize.Regular.evaluation interpretation.domain interpretation.value _ = _
  rw [← bound]
  exact Specialize.Regular.evaluation_coefficient _ _ _

/-- Regular interpretation supports division by every represented value
whose image remains nonzero, with the expected inverse value. -/
theorem regular_inv [DecidableEq F] [DecidableEq G]
    (interpretation : CoefficientMap F G) (a : F)
    (member : a ∈ interpretation.regular.domain) (nonzero : interpretation.regular.map a ≠ 0) :
    a⁻¹ ∈ interpretation.regular.domain ∧
      interpretation.regular.map a⁻¹ = (interpretation.regular.map a)⁻¹ := by
  have valueNonzero : interpretation.regular.value ⟨a, member⟩ ≠ 0 := by
    rwa [← map_mem interpretation.regular a member]
  have inverse := Specialize.Regular.inv_mem interpretation.domain interpretation.value
    ⟨a, member⟩ valueNonzero
  have sourceNonzero : a ≠ 0 := by
    intro zero
    rw [zero, map_zero] at nonzero
    exact nonzero rfl
  refine ⟨inverse, ?_⟩
  apply mul_left_cancel₀ nonzero
  rw [← map_mul interpretation.regular member inverse, mul_inv_cancel₀ sourceNonzero,
    map_one, mul_inv_cancel₀ nonzero]

/-- Restricting regular fractions to a field inclusion preserves inverse
membership and values whenever the interpreted denominator is nonzero. -/
theorem regular_comap_inv {E : Type} [Field E] [DecidableEq E]
    [DecidableEq F] [DecidableEq G] (interpretation : CoefficientMap F G)
    (embedding : E →+* F) (a : E)
    (member : a ∈ (interpretation.regular.comap embedding).domain)
    (nonzero : (interpretation.regular.comap embedding).map a ≠ 0) :
    a⁻¹ ∈ (interpretation.regular.comap embedding).domain ∧
      (interpretation.regular.comap embedding).map a⁻¹ =
        ((interpretation.regular.comap embedding).map a)⁻¹ := by
  rw [comap_domain] at member
  rw [comap_map] at nonzero
  obtain ⟨inverse, mapped⟩ := interpretation.regular_inv (embedding a) member nonzero
  constructor
  · rw [comap_domain, map_inv₀]
    exact inverse
  · rw [comap_map, map_inv₀, mapped, comap_map]

/-- info: 'Hex.RealClosure.CoefficientMap.regular_comap_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.CoefficientMap.regular_comap_inv

/-- info: 'Hex.RealClosure.CoefficientMap.regular_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.CoefficientMap.regular_inv

/-- info: 'Hex.RealClosure.CoefficientMap.regular_map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.CoefficientMap.regular_map

end Hex.RealClosure.CoefficientMap
