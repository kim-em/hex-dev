/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.SourceSelectionConformance
import HexRCF.NativeSamplesConformance

/-! Oracle: the existing native square-root section and its independently
proved real value. The four-coordinate selector is generated, with an actual
inherited identity, computed field coordinates and a joint original guard.
Native execution is diagnostic; the real conclusion uses ordinary proofs. -/
namespace Hex.RCF.SourceSelectionNative
open Hex Hex.RealClosure Hex.RealFormula Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests
open scoped HexMvPolyTheory
abbrev sample := NativeSamplesConformance.sample
abbrev context := sample.input.context
noncomputable abbrev model : Tower.Model context ℝ := NativeSamplesConformance.conversion.target
noncomputable abbrev following : context.origin.base.Realization := NativeSamplesConformance.Point.following
abbrev inputs := SourceSelectionConformance.inputs
noncomputable abbrev source := SourceSelectionConformance.source

def values : Fin 4 → context.Value :=
  ![sample.value, -sample.value, sample.input.value 2, sample.value * sample.value - 1]

theorem point : model.value sample.value = Real.sqrt 2 :=
  NativeSamplesConformance.point.trans Data.selectedSqrt

theorem values_real : model.value ∘ values = source := by
  funext i
  fin_cases i
  · exact point
  · change model.value (-sample.value) = -Real.sqrt 2
    rw [model.neg, point]
  · change model.value (sample.input.value 2) = 2
    exact (NativeSamplesConformance.conversion.value (2 : Data.base.Value)).trans
      (Data.rational.nat 2)
  · change model.value (sample.value * sample.value - 1) = 1
    rw [model.sub, model.mul, model.one, point]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

def matrix : RealFormula.QF 5 :=
  let x : RealFormula.Poly 5 := MvPoly.X 4
  .and (.atom ⟨x - MvPoly.X 0, .eq⟩)
    (.and (.atom ⟨x - 1, .gt⟩) (.atom ⟨x - 2, .lt⟩))

theorem truth : Samples.Row.eval (.and inputs.formula.lift matrix)
    (NativeSpecialize.row context values sample.value (.and inputs.formula.lift matrix)) =
      some true := by
  apply (Samples.Row.eval_true _ _ _ (NativeSpecialize.row_model model values sample.value _)).mpr
  change inputs.formula.lift.toProp
    (RealFormula.append (model.value ∘ values) (model.value sample.value)) ∧
    matrix.toProp (RealFormula.append (model.value ∘ values) (model.value sample.value))
  rw [values_real, point]
  refine ⟨(inputs.formula.lift_correct _ _).mpr SourceSelectionConformance.authenticated, ?_⟩
  have above : 1 < Real.sqrt (2 : ℝ) := by
    rw [← Data.selectedSqrt]
    exact Data.selectedFacts.2.1
  have below : Real.sqrt (2 : ℝ) < 2 := by
    rw [← Data.selectedSqrt]
    exact Data.selectedFacts.2.2
  dsimp only [matrix, RealFormula.QF.toProp, RealFormula.Atom.toProp, RealFormula.Cmp.toProp]
  unfold RealFormula.Poly.eval
  simp_rw [← HexMvPolyTheory.eval₂_toMvPolynomial]
  simpa [HexMvPolyTheory.toMvPolynomial_X, HexMvPolyTheory.toMvPolynomial_sub,
    HexMvPolyTheory.toMvPolynomial_one, RealFormula.append, source,
    SourceSelectionConformance.source, sub_pos, sub_lt_zero,
    show (2 : RealFormula.Poly 5) = MvPoly.C 2 from rfl] using And.intro above below

def divisor : context.Value := values 2 - values 0
theorem nonzero : context.sign divisor ≠ 0 := by
  rw [model.sign]
  have mapped : model.value divisor = 2 - Real.sqrt 2 := by
    rw [divisor, model.sub]
    exact congrArg₂ (fun a b : ℝ => a-b) (congrFun values_real 2) (congrFun values_real 0)
  rw [mapped]
  have below : Real.sqrt (2 : ℝ) < 2 := by
    rw [← Data.selectedSqrt]
    exact Data.selectedFacts.2.2
  simp only [_root_.sign_pos (sub_pos.mpr below), SignType.coe_one, ne_eq, one_ne_zero, not_false_eq_true]

/-- One ordinary point retains the selected embedding, both computed
coordinates, the inherited value and the original nonzero divisor. -/
theorem witness : ∃ x : ℝ, x = Real.sqrt 2 ∧ 1 < x ∧ x < 2 ∧ 2-x ≠ 0 := by
  obtain ⟨read, domain, closed, fixed, present, meaning, guarded⟩ :=
    inputs.exists_real context following values source SourceSelectionConformance.authenticated
      (by
        intro i inherited
        have same := (SourceSelectionConformance.inherited_exact i).mp inherited
        subst i
        exact NativeSamplesConformance.Point.coordinate)
      sample.value matrix [divisor]
      (fun a ha => by simpa only [List.mem_singleton.mp ha] using nonzero) truth
  have guard := (guarded divisor (by simp)).2
  have mapped : read divisor = 2 - read sample.value := by
    change read (values 2 - sample.value) = _
    rw [closed.read_sub _ _ (fixed 2).1 present, (fixed 2).2]
    rfl
  rw [mapped] at guard
  have claims : read sample.value = Real.sqrt 2 ∧
      1 < read sample.value ∧ read sample.value < 2 := by
    dsimp only [matrix, RealFormula.QF.toProp, RealFormula.Atom.toProp,
      RealFormula.Cmp.toProp] at meaning
    unfold RealFormula.Poly.eval at meaning
    simp_rw [← HexMvPolyTheory.eval₂_toMvPolynomial] at meaning
    simpa [HexMvPolyTheory.toMvPolynomial_X, HexMvPolyTheory.toMvPolynomial_sub,
      HexMvPolyTheory.toMvPolynomial_one, RealFormula.append, source,
      SourceSelectionConformance.source, sub_eq_zero, sub_pos, sub_lt_zero,
      show (2 : RealFormula.Poly 5) = MvPoly.C 2 from rfl] using meaning
  exact ⟨read sample.value, claims.1, claims.2.1, claims.2.2, guard⟩

#guard Samples.Row.eval (.and inputs.formula.lift matrix)
  (NativeSpecialize.row context values sample.value (.and inputs.formula.lift matrix)) == some true

run_meta do
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies #[``witness]
  for law in #[``SourceSelection.exists_real,``SourceSelection.unique,
      ``NativeSources.true_real,``truth,``nonzero,``NativeSamplesConformance.Point.coordinate] do
    unless dependencies.contains law do
      Lean.throwError m!"native tuple omitted its selected/source/row/guard law: {law}"
  let axioms ← Lean.collectAxioms ``witness
  unless axioms.size == 3 && axioms.all
      (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
    Lean.throwError m!"native tuple has unexpected axioms: {axioms}"

end Hex.RCF.SourceSelectionNative
