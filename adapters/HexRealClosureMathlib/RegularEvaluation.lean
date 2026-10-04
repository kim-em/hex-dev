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

end Hex.RealClosure.CoefficientMap
