/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TowerModel
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Integral

public section

namespace Hex.RealClosure.Tower.Model

open HexPolyMathlib.Interpret

variable {registry : BaseContext.Registry} {K : Type u}
variable [Field K] [LinearOrder K] [DecidableEq K]
variable {context : Context registry} (model : Model context K)

omit [DecidableEq K] in
theorem toValue_zero (a : context.Value) : model.toValue a = 0 ↔ a = 0 := by
  rw [Subtype.ext_iff]
  simpa only [coe_toValue, Subfield.coe_zero] using model.zero_iff a

/-- Interpret a native polynomial over the predecessor's mathematical field. -/
noncomputable def polynomial (p : DensePoly context.Value) : Polynomial model.field :=
  interpret model.toValue model.toValue_zero p

/-- The semantic polynomial retains every native coefficient's value. -/
@[simp] theorem polynomial_coeff (p : DensePoly context.Value) (i : Nat) :
    (model.polynomial p).coeff i = model.toValue (p.coeff i) := by
  simp only [polynomial, coeff_interpret]

/-- Coercing these coefficients gives the original ambient interpretation. -/
theorem polynomial_map (p : DensePoly context.Value) :
    (model.polynomial p).map model.field.subtype = interpret model.value model.zero_iff p := by
  apply Polynomial.ext
  intro i
  simp only [polynomial, Polynomial.coeff_map, coeff_interpret]
  exact model.coe_toValue (p.coeff i)

theorem polynomial_eval (p : DensePoly context.Value) (a : K) :
    Polynomial.aeval a (model.polynomial p) =
      (interpret model.value model.zero_iff p).eval a := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
    Subfield.algebraMap_ofSubfield, model.polynomial_map]

section Base
variable {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
variable (base : BaseContext.Context registry B sign)
variable (f : letI : Field B := HexPolyMathlib.fieldOfGrind; B →+* K)
variable (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))

omit [DecidableEq K] in
/-- Every canonical base-model value is algebraic over that same base map. -/
theorem base_algebraic :
    letI : Field B := HexPolyMathlib.fieldOfGrind
    letI : Algebra B K := f.toAlgebra
    ∀ a : (Context.base base).Value, IsAlgebraic B ((Model.base base f hsign).value a) := by
  let : Field B := HexPolyMathlib.fieldOfGrind
  let : Algebra B K := f.toAlgebra
  intro a
  have hv := Model.base_value base f hsign a
  rw [hv]
  exact isAlgebraic_algebraMap a.stored
end Base

variable [IsStrictOrderedRing K] [IsRealClosed K]
variable (descriptor : SignDet.Descriptor context.Value Signature context.sign context.signature)

/-- The selected generator is algebraic over the predecessor's entire field,
including when its squarefree defining polynomial is reducible or nonmonic. -/
theorem generator_algebraic :
    IsAlgebraic model.field ((model.adjoin descriptor).value (context.adjoin descriptor).generator) := by
  refine ⟨model.polynomial descriptor.raw.head, ?_, ?_⟩
  · intro h
    have hn := descriptor.head_ne_zero model.value model.zero_iff
    rw [← model.polynomial_map, h, Polynomial.map_zero] at hn
    exact hn rfl
  · rw [model.polynomial_eval, model.adjoin_generator]
    let native := Algebraic.Context.adjoin descriptor context.isClean
    simpa only [native, Algebraic.Context.evalPoly, Algebraic.Context.rootValue,
      Algebraic.Context.root_adjoin] using
      native.evalPoly_head model.value model.zero_iff model.one model.add model.sub
        model.mul model.nat model.sign

/-- Every value of the native child is algebraic over the predecessor's full
mathematical field, by its actual stored polynomial and selected root. -/
theorem adjoin_algebraic (a : (context.adjoin descriptor).context.Value) :
    IsAlgebraic model.field ((model.adjoin descriptor).value a) := by
  obtain ⟨p, hp⟩ := model.adjoin_polynomial descriptor a
  rw [hp, ← model.polynomial_eval]
  let closed := Subalgebra.algebraicClosure model.field K
  let generator : closed :=
    ⟨(model.adjoin descriptor).value (context.adjoin descriptor).generator,
      model.generator_algebraic descriptor⟩
  have h := (Polynomial.aeval generator (model.polynomial p)).property
  rw [← Subalgebra.aeval_coe] at h
  exact h

/-- The whole child value field is algebraic over its predecessor inside the
supplied ambient field. Membership supplies an actual native representative. -/
theorem field_algebraic (a : (model.adjoin descriptor).field) :
    IsAlgebraic model.field (a : K) := by
  obtain ⟨x, hx⟩ := a.property
  rw [← hx]
  exact model.adjoin_algebraic descriptor x

/-- Adjoining a selected root preserves algebraicity over a fixed base when
all predecessor values are algebraic over that base. -/
theorem adjoin_algebraic_over {B : Type v} [Field B] [Algebra B K]
    (halgebraic : ∀ a : context.Value, IsAlgebraic B (model.value a))
    (a : (context.adjoin descriptor).context.Value) :
    IsAlgebraic B ((model.adjoin descriptor).value a) := by
  let U := algebraicClosure B K
  have hle : model.field ≤ U.toSubfield := by
    rintro x ⟨y, hy⟩
    exact mem_algebraicClosure_iff.mpr (by rw [← hy]; exact halgebraic y)
  have ha : IsAlgebraic U ((model.adjoin descriptor).value a) :=
    letI : Algebra model.field U := (Subfield.inclusion hle).toAlgebra
    letI : IsScalarTower model.field U K := .of_algebraMap_eq fun _ => rfl
    (model.adjoin_algebraic descriptor a).extendScalars
      (Subfield.inclusion hle).injective
  exact ha.restrictScalars B

/-- The whole child value field remains algebraic over the fixed base. -/
theorem field_algebraic_over {B : Type v} [Field B] [Algebra B K]
    (halgebraic : ∀ a : context.Value, IsAlgebraic B (model.value a))
    (a : (model.adjoin descriptor).field) : IsAlgebraic B (a : K) := by
  obtain ⟨x, hx⟩ := a.property
  rw [← hx]
  exact model.adjoin_algebraic_over descriptor halgebraic x

end Hex.RealClosure.Tower.Model

/-- info: 'Hex.RealClosure.Tower.Model.generator_algebraic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.generator_algebraic
/-- info: 'Hex.RealClosure.Tower.Model.base_algebraic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.base_algebraic
/-- info: 'Hex.RealClosure.Tower.Model.field_algebraic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.field_algebraic
/-- info: 'Hex.RealClosure.Tower.Model.adjoin_algebraic_over' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.adjoin_algebraic_over
/-- info: 'Hex.RealClosure.Tower.Model.field_algebraic_over' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.field_algebraic_over
