/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TowerAlgebraic
public import HexRealClosureMathlib.CoefficientMap
public import HexRealClosureMathlib.TransportClosed

public section

namespace Hex.RealClosure.Tower.Model

variable {registry : BaseContext.Registry} {context : Context registry}
variable {K G : Type} [Field K] [LinearOrder K] [DecidableEq K]
variable [Field G] [DecidableEq G]

/-- Read native coefficients through their actual semantic value field and
a coefficient interpretation on its subring. -/
noncomputable def read (model : Model context K) (interpretation : CoefficientMap model.field G)
    (a : context.Value) : G := interpretation.map (model.toValue a)

/-- The native coefficients whose semantic values have an interpretation. -/
def domain (model : Model context K) (interpretation : CoefficientMap model.field G)
    (a : context.Value) : Prop := model.toValue a ∈ interpretation.domain

/-- Every polynomial over the actual semantic field has a finite native
coefficient representative. This requires no field structure on native values. -/
theorem polynomial_surjective (model : Model context K) :
    Function.Surjective model.polynomial := by
  classical
  intro p
  let coefficient (i : Fin (p.natDegree + 1)) : context.Value :=
    (model.toValue_surjective (p.coeff i)).choose
  have represents (i : Fin (p.natDegree + 1)) :
      model.toValue (coefficient i) = p.coeff i :=
    (model.toValue_surjective (p.coeff i)).choose_spec
  refine ⟨DensePoly.ofCoeffs (Array.ofFn coefficient), ?_⟩
  apply Polynomial.ext
  intro i
  rw [model.polynomial_coeff, DensePoly.coeff_ofCoeffs]
  change model.toValue ((Array.ofFn coefficient).getD i (0 : context.Value)) = p.coeff i
  by_cases bound : i < p.natDegree + 1
  · rw [← Array.getElem_eq_getD (h := show i < (Array.ofFn coefficient).size from
      by simpa only [Array.size_ofFn] using bound) (0 : context.Value)]
    simpa only [Array.getElem_ofFn] using represents ⟨i, bound⟩
  · rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simpa using Nat.le_of_not_gt bound)]
    simp only [Option.getD_none]
    rw [(model.toValue_zero 0).mpr rfl,
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

omit [DecidableEq G] in
/-- A native polynomial whose stored coefficients lie in the interpretation
domain has a polynomial lift over that subring. -/
theorem polynomial_lift (model : Model context K)
    (interpretation : CoefficientMap model.field G) (p : DensePoly context.Value)
    (guards : ∀ i < p.size, model.domain interpretation (p.coeff i)) :
    ∃ q : Polynomial interpretation.domain,
      q.map interpretation.domain.subtype =
        model.polynomial p := by
  classical
  apply Polynomial.mem_lifts _ |>.mp
  apply Polynomial.lifts_iff_coeff_lifts _ |>.mpr
  intro i
  refine ⟨⟨model.toValue (p.coeff i), ?_⟩, ?_⟩
  · by_cases stored : i < p.size
    · exact guards i stored
    · rw [DensePoly.coeff_eq_zero_of_size_le p (Nat.le_of_not_gt stored)]
      have zero : model.toValue (0 : context.Value) = 0 :=
        (model.toValue_zero 0).mpr rfl
      change model.toValue (0 : context.Value) ∈ interpretation.domain
      rw [zero]
      exact interpretation.domain.zero_mem
  · rw [model.polynomial_coeff]
    rfl

/-- Every lift specializes to the actual native coefficient substitution. -/
theorem polynomial_specialize (model : Model context K)
    (interpretation : CoefficientMap model.field G) (p : DensePoly context.Value)
    (q : Polynomial interpretation.domain)
    (lift : q.map interpretation.domain.subtype =
      model.polynomial p) :
    HexPolyMathlib.toPolynomial (Transport.polynomial (model.read interpretation) p) =
      q.map interpretation.value := by
  classical
  have zero : model.read interpretation 0 = 0 := by
    unfold read
    rw [(model.toValue_zero 0).mpr rfl, interpretation.map_zero]
  ext i
  rw [HexPolyMathlib.coeff_toPolynomial, Transport.polynomial_coeff _ zero,
    Polynomial.coeff_map]
  have coefficient := congrArg (fun p => p.coeff i) lift
  simp only [Polynomial.coeff_map, model.polynomial_coeff] at coefficient
  unfold read
  rw [← coefficient]
  change interpretation.map (q.coeff i : model.field) = interpretation.value (q.coeff i)
  exact interpretation.map_mem (q.coeff i : model.field) (q.coeff i).property

/-- Semantic arithmetic supplies the closed interpretation domain needed by
the existing raw-coefficient certificate transport, without a field instance
on native tower syntax. -/
theorem closed (model : Model context K) (interpretation : CoefficientMap model.field G) :
    Transport.Closed (model.read interpretation) (model.domain interpretation) := by
  have zero : model.toValue (0 : context.Value) = 0 :=
    Subtype.ext ((model.zero_iff 0).mpr rfl)
  have one : model.toValue (1 : context.Value) = 1 := Subtype.ext model.one
  have add a b : model.toValue (a + b) = model.toValue a + model.toValue b :=
    Subtype.ext (model.add a b)
  have mul a b : model.toValue (a * b) = model.toValue a * model.toValue b :=
    Subtype.ext (model.mul a b)
  have sub a b : model.toValue (a - b) = model.toValue a - model.toValue b :=
    Subtype.ext (model.sub a b)
  have natCast (n : Nat) : model.toValue (n : context.Value) = (n : model.field) :=
    Subtype.ext (model.nat n)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change model.toValue 0 ∈ interpretation.domain
    rw [zero]
    exact interpretation.domain.zero_mem
  · intro a b ha hb
    change model.toValue (a + b) ∈ interpretation.domain
    rw [add]
    exact interpretation.domain.add_mem ha hb
  · intro a b ha hb
    change model.toValue (a * b) ∈ interpretation.domain
    rw [mul]
    exact interpretation.domain.mul_mem ha hb
  · intro a b ha hb
    change model.toValue (a - b) ∈ interpretation.domain
    rw [sub]
    exact interpretation.domain.sub_mem ha hb
  · change model.toValue 1 ∈ interpretation.domain
    rw [one]
    exact interpretation.domain.one_mem
  · intro n
    change model.toValue (n : context.Value) ∈ interpretation.domain
    rw [natCast]
    exact (n : interpretation.domain).property
  · unfold read
    rw [zero]
    exact interpretation.map_zero
  · intro a b ha hb
    unfold read
    rw [add]
    exact interpretation.map_add ha hb
  · intro a b ha hb
    unfold read
    rw [mul]
    exact interpretation.map_mul ha hb
  · intro a b ha hb
    unfold read
    rw [sub]
    exact interpretation.map_sub ha hb
  · unfold read
    rw [one]
    exact interpretation.map_one
  · intro n
    unfold read
    rw [natCast, interpretation.map_mem (n : model.field) (natCast_mem interpretation.domain n)]
    change interpretation.value (n : interpretation.domain) = (n : G)
    exact map_natCast interpretation.value n

/-- info: 'Hex.RealClosure.Tower.Model.closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.closed

/-- info: 'Hex.RealClosure.Tower.Model.polynomial_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.polynomial_surjective

/-- info: 'Hex.RealClosure.Tower.Model.polynomial_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.polynomial_lift

/-- info: 'Hex.RealClosure.Tower.Model.polynomial_specialize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.polynomial_specialize

end Hex.RealClosure.Tower.Model
