/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients
public import HexRCF.SourceSelectionCases
public meta import HexRCF.RealCoefficients
public meta import HexRCF.SourceSelectionCases
public section

/-! Oracle: the owner's checked selected-field factory and its model laws;
mode: always. Public-module consumer and compiled execution of actual fixed-field
packing, generated source selection, matrix shifting and selector-only refusal.
Compiled observations are separate from the ordinary interpretation theorems. -/
namespace Hex.RCF.FieldSelectionConformance
open Hex Hex.RealClosure Hex.RealFormula Hex.RCF.RealCoefficients

def registry : BaseContext.Registry := fun _ => none
@[expose] def root := SourceSelectionCases.root
@[expose] def coordinates : Fin 3 → QAdjoin root.toCanonical.toAlgebraic :=
  let a := root.toCanonical.toAlgebraic.toQAdjoin
  ![-a,2,a*a-1]

@[expose] noncomputable def source : Fin 4 → ℝ := ![Real.sqrt 2,-Real.sqrt 2,2,1]

theorem root_real : root.real = Real.sqrt 2 := SourceSelectionCases.selected

theorem source_eq : FieldSelection.source root coordinates = source := by
  funext i
  fin_cases i
  · exact (Root.toCanonical_real root).trans SourceSelectionCases.selected
  · change (Coefficients.ofField root.toCanonical (-root.toCanonical.toAlgebraic.toQAdjoin)).toReal = -Real.sqrt 2
    rw [← NumberField.value_eq_ofField, Hex.RealClosure.NumberField.value_neg,
      NumberField.value_eq_ofField, Coefficients.ofField_gen,
      Root.toCanonical_real, root_real]
  · change (Coefficients.ofField root.toCanonical (2 : QAdjoin root.toCanonical.toAlgebraic)).toReal = 2
    rw [← NumberField.value_eq_ofField]
    exact Hex.RealClosure.NumberField.value_nat root.toCanonical 2
  · change (Coefficients.ofField root.toCanonical
      (root.toCanonical.toAlgebraic.toQAdjoin * root.toCanonical.toAlgebraic.toQAdjoin - 1)).toReal = 1
    rw [← NumberField.value_eq_ofField, Hex.RealClosure.NumberField.value_sub,
      Hex.RealClosure.NumberField.value_mul, Hex.RealClosure.NumberField.value_one,
      NumberField.value_eq_ofField, Coefficients.ofField_gen,
      Root.toCanonical_real, root_real]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

def original : RealFormula.QF 4 :=
  let x : RealFormula.Poly 4 := MvPoly.X 3
  .and (.atom ⟨x - MvPoly.X 2, .eq⟩)
    (.and (.atom ⟨MvPoly.X 0 + MvPoly.X 1, .gt⟩)
      (.atom ⟨MvPoly.X 2 - 1, .eq⟩))

/-- This consumer imports no private implementation bodies. -/
theorem authentication
    (presentation : Hex.RealClosure.NumberField.Presentation root.toCanonical registry) :
    (FieldSelection.prepare root coordinates).formula.toProp
      (presentation.model.value ∘ FieldSelection.nativeValues root presentation coordinates) :=
  FieldSelection.native_authenticated root presentation coordinates

theorem matrix_identity (values : Fin 3 → ℝ) (generator x : ℝ) :
    (FieldSelection.matrix original).toProp
      (RealFormula.append (Fin.cases generator values) x) ↔
      original.toProp (RealFormula.append values x) :=
  FieldSelection.matrix_correct original generator values x

noncomputable def presentation : Hex.RealClosure.NumberField.Presentation root.toCanonical registry :=
  Classical.choose (Hex.RealClosure.NumberField.present?_success root.toCanonical registry)

/-- The proof fixture is an actual successful result of the same factory
executed below; it is not an independently fabricated presentation. -/
theorem manufactured : Hex.RealClosure.NumberField.present? root.toCanonical registry = some presentation :=
  Classical.choose_spec (Hex.RealClosure.NumberField.present?_success root.toCanonical registry)

noncomputable def values := FieldSelection.nativeValues root presentation coordinates
noncomputable def sample := presentation.pack (1 : QAdjoin root.toCanonical.toAlgebraic)

theorem sample_real : presentation.model.value sample = 1 :=
  (presentation.pack_value (1 : QAdjoin root.toCanonical.toAlgebraic)).trans
    (Hex.RealClosure.NumberField.value_one root.toCanonical)

theorem point_truth : Samples.Row.eval
    (.and (FieldSelection.prepare root coordinates).formula.lift (FieldSelection.matrix original))
    (NativeSpecialize.row presentation.context values sample
      (.and (FieldSelection.prepare root coordinates).formula.lift (FieldSelection.matrix original))) =
      some true := by
  apply (Samples.Row.eval_true _ _ _
    (NativeSpecialize.row_model presentation.model values sample _)).mpr
  change (FieldSelection.prepare root coordinates).formula.lift.toProp
      (RealFormula.append (presentation.model.value ∘ values) (presentation.model.value sample)) ∧
    (FieldSelection.matrix original).toProp
      (RealFormula.append (presentation.model.value ∘ values) (presentation.model.value sample))
  have interpreted := FieldSelection.nativeValues_real root presentation coordinates
  change presentation.model.value ∘ values = _ at interpreted
  rw [interpreted, sample_real]
  refine ⟨((FieldSelection.prepare root coordinates).formula.lift_correct _ _).mpr
    (FieldSelection.authenticated root coordinates), ?_⟩
  apply (FieldSelection.matrix_correct original root.toCanonical.toReal _ _).mpr
  have same : (fun i => (Coefficients.ofField root.toCanonical (coordinates i)).toReal) =
      fun i : Fin 3 => source i.succ := by
    funext i
    exact congrFun source_eq i.succ
  rw [same]
  have below : Real.sqrt (2 : ℝ) < 2 := by nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg (2 : ℝ)]
  dsimp only [original, RealFormula.QF.toProp, RealFormula.Atom.toProp, RealFormula.Cmp.toProp]
  unfold RealFormula.Poly.eval
  simp_rw [← HexMvPolyTheory.eval₂_toMvPolynomial]
  norm_num [HexMvPolyTheory.toMvPolynomial_X, HexMvPolyTheory.toMvPolynomial_sub,
    HexMvPolyTheory.toMvPolynomial_add, HexMvPolyTheory.toMvPolynomial_one,
    RealFormula.append, source]

theorem point_witness : ∃ x : ℝ, original.toProp
    (RealFormula.append (fun i => (Coefficients.ofField root.toCanonical (coordinates i)).toReal) x) := by
  obtain ⟨x, meaning, _⟩ := FieldSelection.true_real root presentation coordinates
    sample original [] (by simp) point_truth
  exact ⟨x, meaning⟩

#eval (show IO Unit from do
  let some presentation := Hex.RealClosure.NumberField.present? root.toCanonical registry
    | throw (IO.userError "original selected generator has no presentation")
  let values := FieldSelection.nativeValues root presentation coordinates
  let plan := FieldSelection.prepare root coordinates
  let sample := presentation.pack (1 : QAdjoin root.toCanonical.toAlgebraic)
  let shifted := FieldSelection.matrix original
  let joint := RealFormula.QF.and plan.formula.lift shifted
  unless presentation.context.sign (sample-values 0) != 0 do
    throw (IO.userError "sample was not distinct from the selected generator")
  unless Samples.Row.eval joint (NativeSpecialize.row presentation.context values sample joint) == some true do
    throw (IO.userError "factory packing or matrix coordinate order changed")
  unless Samples.Row.eval plan.formula.lift
      (NativeSpecialize.row presentation.context values sample plan.formula.lift) == some true do
    throw (IO.userError "generated selector rejected its actual packed tuple")
  let swapped : Fin 4 → presentation.context.Value := fun i =>
    if i = 1 then values 3 else if i = 3 then values 1 else values i
  unless Samples.Row.eval plan.formula.lift
      (NativeSpecialize.row presentation.context swapped sample plan.formula.lift) == some false do
    throw (IO.userError "selector alone failed to reject swapped computed coordinates")
  IO.println "actual Presentation factory/packing, distinct sample, shifted matrix and selector-only swap checked")

end Hex.RCF.FieldSelectionConformance
