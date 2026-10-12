/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.NativeSelection
import HexRCF.NativeSourcesConformance
/-! Oracle: the existing frozen positive sqrt2 descriptor and independent
selected-value facts; mode: always. Exercises exact ordered constraints,
wrong-conjugate native rows, finite-reader composition, polynomial relations
and malformed sign/list data. Non-module imports expose private fixture bodies
in the pinned toolchain; this does not attest a public-only frozen fixture.
Kernel proofs and compiled controls are separate. -/
namespace Hex.RCF.RealCoefficients.NativeSelectionConformance
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.RealFormula
open Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests
open NativeSourcesConformance

def projection (a : Data.base.Value) : Rat := a.stored
theorem reflection (a : Data.base.Value) : projection a = 0 ↔ a = 0 :=
  BaseContext.Element.stored_eq_zero a

theorem projected_value : ratCast ∘ projection = Data.rational.value := by
  funext a
  exact (Tower.Model.base_value (BaseContext.rational Data.registry) (Rat.castHom ℝ)
    Hex.RealClosure.ratSign a).symm

theorem projected_signs (qs : List Data.base.Poly) (x : ℝ) :
    SignDet.signsAt (ratCast ∘ projection) (fun a => (ratZero (projection a)).trans (reflection a))
      qs x = SignDet.signsAt Data.rational.value Data.rational.zero_iff qs x :=
  NativeSelection.signs_projected projection reflection Data.rational.value
    Data.rational.zero_iff projected_value qs x

def selection : RealFormula.QF 1 :=
  NativeSelection.translate projection reflection 0 Data.lower.raw.constraints
    Data.lower.raw.constraintSigns

theorem selected : selection.toProp (fun _ => Real.sqrt 2) := by
  apply (NativeSelection.translate_identity projection reflection Data.lower
    Data.rational.value Data.rational.zero_iff Data.rational.one Data.rational.add
    Data.rational.sub Data.rational.mul Data.rational.nat Data.rational.sign projected_value 0 _).mpr
  exact Data.selectedSqrt.symm

theorem unique (values : Fin 1 → ℝ) (meaning : selection.toProp values) :
    values = fun _ => Real.sqrt 2 := by
  have same := (NativeSelection.translate_identity projection reflection Data.lower
    Data.rational.value Data.rational.zero_iff Data.rational.one Data.rational.add
    Data.rational.sub Data.rational.mul Data.rational.nat Data.rational.sign projected_value 0 values).mp
      meaning
  change values 0 = Data.selectedReal at same
  rw [Data.selectedSqrt] at same
  funext i
  fin_cases i
  exact same

theorem wrong_conjugate : ¬ selection.toProp (fun _ => -Real.sqrt 2) := by
  intro meaning
  have same := congrFun (unique _ meaning) 0
  have positive : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  linarith

noncomputable abbrev model : Tower.Model context ℝ := NativeSamplesConformance.Nested.conversion.target
def values : Fin 1 → context.Value := sample.input.value ∘ Upper.values

theorem row_model (coordinates : Fin 1 → context.Value) (formula : RealFormula.QF 2) :
    NativeSpecialize.row context coordinates sample.value formula = formula.polys.map
      (fun q => (SignType.sign (q.eval
        (RealFormula.append (model.value ∘ coordinates) (model.value sample.value))) : Int)) := by
  unfold NativeSpecialize.row RepresentationSpecialize.prepare
  simp only [List.map_map]
  apply List.map_congr_left
  intro q _
  dsimp only [Function.comp_def]
  erw [model.sign, ← HexPolyMathlib.Interpret.eval_interpret model.value model.zero_iff model.add model.mul]
  change (SignType.sign (RepresentationSpecialize.evaluate model.value model.zero_iff
    (model.value sample.value) (RepresentationSpecialize.polynomial coordinates q)) : Int) = _
  rw [RepresentationSpecialize.polynomial_eval model.value model.zero_iff model.one
    model.add model.mul model.nat model.neg]

theorem truth : Samples.Row.eval (.and selection.lift Upper.schema)
    (NativeSpecialize.row context values sample.value (.and selection.lift Upper.schema)) =
      some true := by
  apply (Samples.Row.eval_true _ _ _ (row_model values _)).mpr
  have coefficient : model.value ∘ values = fun _ => Real.sqrt 2 := by
    funext i
    exact NativeSamplesConformance.Nested.coefficient_fixed
  have point : model.value sample.value = CatalogSource.selected.denote Data.original :=
    NativeSamplesConformance.Nested.point
  change selection.lift.toProp (RealFormula.append (model.value ∘ values) (model.value sample.value)) ∧
    Upper.schema.toProp (RealFormula.append (model.value ∘ values) (model.value sample.value))
  constructor
  · rw [coefficient]
    exact (selection.lift_correct _ _).mpr selected
  · rw [coefficient, point]
    dsimp only [Upper.schema, RealFormula.QF.toProp, RealFormula.Atom.toProp, RealFormula.Cmp.toProp]
    unfold RealFormula.Poly.eval
    simp_rw [← HexMvPolyMathlib.eval₂_toMvPolynomial]
    have actual := CatalogSource.source
    simpa [HexMvPolyMathlib.toMvPolynomial_X, HexMvPolyMathlib.toMvPolynomial_sub,
      HexMvPolyMathlib.toMvPolynomial_pow, HexMvPolyMathlib.toMvPolynomial_one,
      show (2 : RealFormula.Poly 2)=MvPoly.C 2 from rfl,
      RealFormula.append, sub_eq_zero, sub_pos, sub_lt_zero] using actual

theorem further_root : ∃ x : ℝ, x^2 = Real.sqrt 2 ∧ 1<x ∧ x<2 := by
  obtain ⟨read, domain, closed, negative, fixed, present, sizes, meaning, guards, base⟩ :=
    NativeSources.true_real context following values (fun _ => Real.sqrt 2) selection
      (fun coefficients _ selected => unique coefficients selected)
      sample.value Upper.schema [] (by simp) truth
  refine ⟨read sample.value, ?_⟩
  dsimp only [Upper.schema, RealFormula.QF.toProp, RealFormula.Atom.toProp, RealFormula.Cmp.toProp] at meaning
  unfold RealFormula.Poly.eval at meaning
  simp_rw [← HexMvPolyMathlib.eval₂_toMvPolynomial] at meaning
  simpa [HexMvPolyMathlib.toMvPolynomial_X, HexMvPolyMathlib.toMvPolynomial_sub,
    HexMvPolyMathlib.toMvPolynomial_pow, HexMvPolyMathlib.toMvPolynomial_one,
    show (2 : RealFormula.Poly 2)=MvPoly.C 2 from rfl,
    RealFormula.append, sub_eq_zero, sub_pos, sub_lt_zero] using meaning

def wrong_values : Fin 1 → context.Value :=
  sample.input.value ∘ NativeSamplesConformance.Nested.wrongValues

theorem wrong_row : Samples.Row.eval (.and selection.lift Upper.schema)
    (NativeSpecialize.row context wrong_values sample.value (.and selection.lift Upper.schema)) =
      some false := by
  obtain ⟨result, accepted, semantic⟩ := Samples.Row.eval_spec _ _ _ (row_model wrong_values _)
  cases result
  · exact accepted
  · have meaning := semantic.mp rfl
    change selection.lift.toProp
      (RealFormula.append (model.value ∘ wrong_values) (model.value sample.value)) ∧ _ at meaning
    have selected := (selection.lift_correct _ _).mp meaning.1
    have coefficient : model.value ∘ wrong_values = fun _ => -Real.sqrt 2 := by
      funext i
      apply (NativeSamplesConformance.Nested.conversion.value
        (NativeSamplesConformance.Nested.wrongValues i)).trans
      dsimp only [NativeSamplesConformance.Nested.wrongValues]
      erw [Data.original.neg, Data.alpha_value]
    rw [coefficient] at selected
    exact False.elim (wrong_conjugate selected)


/-- Dropping the actual frozen endpoint sign refuses the actual native row. -/
def incomplete : RealFormula.QF 1 := NativeSelection.translate projection reflection 0
  Data.lower.raw.constraints Data.lower.raw.constraintSigns.dropLast
#guard Samples.Row.eval incomplete.lift
  (NativeSpecialize.row context values sample.value incomplete.lift) == some false

/-- Flipping the last actual frozen endpoint sign falsifies the actual row. -/
def flipped : RealFormula.QF 1 := NativeSelection.translate projection reflection 0
  Data.lower.raw.constraints (Data.lower.raw.constraintSigns.dropLast ++ [1])
#guard Samples.Row.eval flipped.lift
  (NativeSpecialize.row context values sample.value flipped.lift) == some false

namespace Derived
open scoped Hex

def polynomial : DensePoly Rat := #p[-1, 0, 1]
def selection : RealFormula.QF 2 :=
  .and Hex.RCF.RealCoefficients.NativeSelectionConformance.selection.lift (NativeSelection.relation 0 1 polynomial)

noncomputable def source : Fin 2 → ℝ := fun i => if i = 0 then Real.sqrt 2 else 1

theorem polynomial_eval (x : ℝ) : (realPoly polynomial).eval x = x^2-1 := by
  unfold realPoly polynomial
  rw [HexPolyMathlib.Interpret.interpret_map, DensePoly.Interpret.map_ofCoeffs,
    HexPolyMathlib.toPolynomial_ofCoeffs]
  simp [ratCast, Finset.sum_range_succ, Array.getD, sub_eq_add_neg, add_comm]

theorem unique (coordinates : Fin 2 → ℝ) (meaning : selection.toProp coordinates) :
    coordinates = source := by
  change Hex.RCF.RealCoefficients.NativeSelectionConformance.selection.lift.toProp coordinates ∧
    (NativeSelection.relation 0 1 polynomial).toProp coordinates at meaning
  have same : RealFormula.append (fun _ : Fin 1 => coordinates 0) (coordinates 1) = coordinates := by
    funext i
    fin_cases i <;> rfl
  have first := congrFun (Hex.RCF.RealCoefficients.NativeSelectionConformance.unique (fun _ => coordinates 0)
    ((Hex.RCF.RealCoefficients.NativeSelectionConformance.selection.lift_correct _ _).mp (by rw [same]; exact meaning.1))) 0
  have second := (NativeSelection.relation_correct 0 1 polynomial coordinates).mp meaning.2
  rw [polynomial_eval, first, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at second
  funext i
  fin_cases i
  · simpa [source] using first
  · norm_num [source] at second ⊢
    exact second

theorem selected : selection.toProp source := by
  change Hex.RCF.RealCoefficients.NativeSelectionConformance.selection.lift.toProp source ∧
    (NativeSelection.relation 0 1 polynomial).toProp source
  constructor
  · have same : RealFormula.append (fun _ : Fin 1 => Real.sqrt 2) 1 = source := by
      funext i
      fin_cases i <;> rfl
    rw [← same]
    exact (Hex.RCF.RealCoefficients.NativeSelectionConformance.selection.lift_correct _ _).mpr Hex.RCF.RealCoefficients.NativeSelectionConformance.selected
  · apply (NativeSelection.relation_correct 0 1 polynomial source).mpr
    rw [polynomial_eval]
    norm_num [source, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- info: 'Hex.RCF.RealCoefficients.NativeSelectionConformance.Derived.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unique
/-- info: 'Hex.RCF.RealCoefficients.NativeSelectionConformance.Derived.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selected
def rationalPolynomial : DensePoly Rat := #p[-(1/5), 0, 1/3]

theorem rational_eval (x : ℝ) :
    (realPoly rationalPolynomial).eval x = x^2/3-1/5 := by
  unfold realPoly rationalPolynomial
  rw [HexPolyMathlib.Interpret.interpret_map, DensePoly.Interpret.map_ofCoeffs,
    HexPolyMathlib.toPolynomial_ofCoeffs]
  simp [ratCast, Finset.sum_range_succ, Array.getD]
  ring

theorem rational_relation (coordinates : Fin 2 → ℝ) :
    (NativeSelection.relation 0 1 rationalPolynomial).toProp coordinates ↔
      coordinates 1 = (coordinates 0)^2/3-1/5 := by
  rw [NativeSelection.relation_correct, rational_eval]

/-- info: 'Hex.RCF.RealCoefficients.NativeSelectionConformance.Derived.rational_relation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rational_relation

#guard Samples.Row.eval (NativeSelection.relation (0 : Fin 2) 1 rationalPolynomial) [0] == some true
theorem rational_literal : NativeSelection.relation (0 : Fin 2) 1 rationalPolynomial =
    RealFormula.QF.atom ⟨15 * MvPoly.X 1 - 5 * MvPoly.X 0 ^ 2 + 3, .eq⟩ := by
  decide +kernel

#guard NativeSelection.relation (0 : Fin 2) 1 rationalPolynomial ==
  RealFormula.QF.atom ⟨15 * MvPoly.X 1 - 5 * MvPoly.X 0 ^ 2 + 3, .eq⟩
end Derived

/-- info: 'Hex.RCF.RealCoefficients.NativeSelectionConformance.projected_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms projected_value
/-- info: 'Hex.RCF.RealCoefficients.NativeSelectionConformance.projected_signs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms projected_signs
/-- info: 'Hex.RCF.RealCoefficients.NativeSelectionConformance.row_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms row_model
/-- info: 'Hex.RCF.RealCoefficients.NativeSelectionConformance.truth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms truth
/-- info: 'Hex.RCF.RealCoefficients.NativeSelectionConformance.further_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms further_root
/-- info: 'Hex.RCF.RealCoefficients.NativeSelectionConformance.wrong_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_row

run_meta do
  for (name, laws) in #[(``unique, #[``NativeSelection.translate_identity]),
      (``further_root, #[``NativeSources.true_real, ``unique, ``truth]),
      (``truth, #[``row_model, ``selected]), (``wrong_row, #[``row_model, ``wrong_conjugate])] do
    let _ ← Hex.RCF.checkProof name (← Lean.Meta.inferType (Lean.mkConst name)) (Lean.mkConst name)
    for law in laws do
      unless ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf law) do
        Lean.throwError "generated selection omitted its actual source, row or finite-reader law"
    let axioms ← Lean.collectAxioms name
    unless axioms.size == 3 && axioms.all
        (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
      Lean.throwError "generated selection has an unexpected complete axiom inventory"

#guard Samples.Row.eval (.and selection.lift Upper.schema)
  (NativeSpecialize.row context values sample.value (.and selection.lift Upper.schema)) == some true
#guard Samples.Row.eval (.and selection.lift Upper.schema)
  (NativeSpecialize.row context wrong_values sample.value (.and selection.lift Upper.schema)) == some false

/-- info: 'Hex.RCF.RealCoefficients.NativeSelectionConformance.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selected
/-- info: 'Hex.RCF.RealCoefficients.NativeSelectionConformance.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unique
/-- info: 'Hex.RCF.RealCoefficients.NativeSelectionConformance.wrong_conjugate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_conjugate

#guard Samples.Row.eval (NativeSelection.signs (0 : Fin 1) [] [0]) [] == some false
#guard Samples.Row.eval (NativeSelection.signs (0 : Fin 1) [0] []) [] == some false
#guard Samples.Row.eval (NativeSelection.signAtom (0 : Fin 1) 0 2) [] == some false
end Hex.RCF.RealCoefficients.NativeSelectionConformance
