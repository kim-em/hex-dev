/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.SourceSelectionConformance
import HexRCF.NativeSamplesConformance
import HexRCF.RealCoefficients.FieldSelection

/-! Oracle: the existing native square-root section and its independently
proved real value. The four-coordinate selector is generated from actual
`QAdjoin` computations without inherited slots, and retains two original guards.
Native execution is diagnostic; the real conclusion uses ordinary proofs. -/
namespace Hex.RCF.SourceSelectionNative
open Hex Hex.RealClosure Hex.RealFormula Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests
open scoped HexMvPolyTheory
abbrev sample := NativeSamplesConformance.sample
abbrev context := sample.input.context
noncomputable abbrev model : Tower.Model context ℝ := NativeSamplesConformance.conversion.target
noncomputable abbrev following : context.origin.base.Realization := NativeSamplesConformance.Point.following
abbrev generator := SourceSelectionCases.root.toCanonical

def coordinates : Fin 3 → QAdjoin generator.toAlgebraic :=
  let a := generator.toAlgebraic.toQAdjoin
  ![-a, 2, a*a-1]

def inputs := FieldSelection.prepare SourceSelectionCases.root coordinates
noncomputable abbrev source := SourceSelectionConformance.source

theorem source_eq : FieldSelection.source SourceSelectionCases.root coordinates = source := by
  funext i
  fin_cases i
  · exact (Root.toCanonical_real SourceSelectionCases.root).trans SourceSelectionCases.selected
  · change (Coefficients.ofField generator (-generator.toAlgebraic.toQAdjoin)).toReal = -Real.sqrt 2
    rw [← NumberField.value_eq_ofField, Hex.RealClosure.NumberField.value_neg,
      NumberField.value_eq_ofField, Coefficients.ofField_gen,
      Root.toCanonical_real, SourceSelectionCases.selected]
  · change (Coefficients.ofField generator (2 : QAdjoin generator.toAlgebraic)).toReal = 2
    rw [← NumberField.value_eq_ofField]
    exact Hex.RealClosure.NumberField.value_nat generator 2
  · change (Coefficients.ofField generator
      (generator.toAlgebraic.toQAdjoin * generator.toAlgebraic.toQAdjoin - 1)).toReal = 1
    rw [← NumberField.value_eq_ofField, Hex.RealClosure.NumberField.value_sub,
      Hex.RealClosure.NumberField.value_mul, Hex.RealClosure.NumberField.value_one,
      NumberField.value_eq_ofField, Coefficients.ofField_gen,
      Root.toCanonical_real, SourceSelectionCases.selected]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem authenticated : inputs.formula.toProp source := by
  rw [← source_eq]
  exact FieldSelection.authenticated SourceSelectionCases.root coordinates

theorem inherited_empty (i : Fin 4) : inputs.isInherited i = false :=
  FieldSelection.inherited_false SourceSelectionCases.root (fun j => (coordinates j).coeffs) i

def values : Fin 4 → context.Value :=
  ![sample.value, -sample.value, sample.input.value 2, sample.value * sample.value - 1]

theorem point : model.value sample.value = Real.sqrt 2 :=
  NativeSamplesConformance.point.trans Data.selectedSqrt

private theorem tuple_value {registry : BaseContext.Registry} {c : Tower.Context registry}
    (m : Tower.Model c ℝ) (a b : c.Value) :
    m.value ∘ ![a,-a,b,a*a-1] =
      ![m.value a,-m.value a,m.value b,m.value a*m.value a-1] := by
  funext i
  fin_cases i
  · rfl
  · exact m.neg a
  · rfl
  · exact (m.sub (a*a) 1).trans (congrArg₂ (fun x y : ℝ => x-y) (m.mul a a) m.one)

theorem values_real : model.value ∘ values = source := by
  have interpreted := tuple_value model sample.value (sample.input.value 2)
  change model.value ∘ values = _ at interpreted
  rw [interpreted, point]
  funext i
  fin_cases i
  · rfl
  · rfl
  · change model.value (sample.input.value 2) = 2
    exact (NativeSamplesConformance.conversion.value (2 : Data.base.Value)).trans
      (Data.rational.nat 2)
  · change Real.sqrt 2 * Real.sqrt 2 - 1 = 1
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

def matrix : RealFormula.QF 5 :=
  let x : RealFormula.Poly 5 := MvPoly.X 4
  .and (.atom ⟨x - MvPoly.X 0, .eq⟩)
    (.and (.atom ⟨x * MvPoly.X 1 + MvPoly.X 2, .eq⟩)
      (.and (.atom ⟨x^2 - MvPoly.X 3 - 1, .eq⟩)
        (.and (.atom ⟨x - 1, .gt⟩) (.atom ⟨x - MvPoly.X 2, .lt⟩))))

theorem truth : Samples.Row.eval (.and inputs.formula.lift matrix)
    (NativeSpecialize.row context values sample.value (.and inputs.formula.lift matrix)) =
      some true := by
  apply (Samples.Row.eval_true _ _ _ (NativeSpecialize.row_model model values sample.value _)).mpr
  change inputs.formula.lift.toProp
    (RealFormula.append (model.value ∘ values) (model.value sample.value)) ∧
    matrix.toProp (RealFormula.append (model.value ∘ values) (model.value sample.value))
  rw [values_real, point]
  refine ⟨(inputs.formula.lift_correct _ _).mpr authenticated, ?_⟩
  have above : 1 < Real.sqrt (2 : ℝ) := by
    rw [← Data.selectedSqrt]
    exact Data.selectedFacts.2.1
  have below : Real.sqrt (2 : ℝ) < 2 := by
    rw [← Data.selectedSqrt]
    exact Data.selectedFacts.2.2
  dsimp only [matrix, RealFormula.QF.toProp, RealFormula.Atom.toProp, RealFormula.Cmp.toProp]
  unfold RealFormula.Poly.eval
  simp_rw [← HexMvPolyTheory.eval₂_toMvPolynomial]
  norm_num [HexMvPolyTheory.toMvPolynomial_X, HexMvPolyTheory.toMvPolynomial_sub,
    HexMvPolyTheory.toMvPolynomial_add, HexMvPolyTheory.toMvPolynomial_mul,
    HexMvPolyTheory.toMvPolynomial_pow, HexMvPolyTheory.toMvPolynomial_one,
    RealFormula.append, source, SourceSelectionConformance.source,
    show (2 : RealFormula.Poly 5) = MvPoly.C 2 from rfl]
  all_goals nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

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

def computedDivisor : context.Value := values 3 - values 1

theorem computed_nonzero : context.sign computedDivisor ≠ 0 := by
  rw [model.sign]
  have mapped : model.value computedDivisor = 1 + Real.sqrt 2 := by
    rw [computedDivisor, model.sub]
    have same := congrArg₂ (fun a b : ℝ => a-b) (congrFun values_real 3) (congrFun values_real 1)
    simpa [Function.comp_def, source, SourceSelectionConformance.source] using same
  rw [mapped]
  have positive : 0 < 1 + Real.sqrt (2 : ℝ) := by nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  simp only [_root_.sign_pos positive, SignType.coe_one, ne_eq, one_ne_zero, not_false_eq_true]

/-- The same reader identifies every computed coordinate and retains both
original closed guards while exporting the matrix that uses those coordinates. -/
theorem reader : ∃ read : context.Value → ℝ, ∃ domain : context.Value → Prop,
    Transport.Closed read domain ∧
    (∀ i, domain (values i) ∧ read (values i) = source i) ∧ domain sample.value ∧
    matrix.toProp (RealFormula.append source (read sample.value)) ∧
    read divisor ≠ 0 ∧ read computedDivisor ≠ 0 := by
  obtain ⟨read, domain, closed, negative, fixed, present, sizes, meaning, guarded, base⟩ :=
    inputs.exists_real context following values source authenticated
      (by
        intro i inherited
        have impossible : (false : Bool) = true := (inherited_empty i).symm.trans inherited
        cases impossible)
      sample.value matrix [divisor,computedDivisor]
      (by
        intro a member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact nonzero
        · exact computed_nonzero) truth
  exact ⟨read, domain, closed, fixed, present, meaning,
    (guarded divisor (by simp)).2, (guarded computedDivisor (by simp)).2⟩

private theorem tuple_first {α : Type} (a b c d : α) : (![a,b,c,d]) 0 = a := rfl

theorem values_first : values 0 = sample.value :=
  tuple_first _ _ _ _

/-- Both computed coordinates contribute to the actual matrix and its real
conclusion, and the two nonzero guards hold at that same point. -/
theorem witness : ∃ x : ℝ, x = Real.sqrt 2 ∧ x * (-Real.sqrt 2) + 2 = 0 ∧
    x^2 - 1 - 1 = 0 ∧ 1 < x ∧ x < 2 ∧ 2-x ≠ 0 ∧ 1+Real.sqrt 2 ≠ 0 := by
  obtain ⟨read, domain, closed, fixed, present, meaning, guarded, computed⟩ := reader
  have mapped : read divisor = 2 - read sample.value := by
    rw [divisor, closed.read_sub _ _ (fixed 2).1 (fixed 0).1,
      (fixed 2).2, (fixed 0).2]
    rw [← (fixed 0).2, values_first]
    rfl
  rw [mapped] at guarded
  have computedValue : read computedDivisor = 1 + Real.sqrt 2 := by
    change read (values 3 - values 1) = _
    rw [closed.read_sub _ _ (fixed 3).1 (fixed 1).1, (fixed 3).2, (fixed 1).2]
    simp [source, SourceSelectionConformance.source]
  rw [computedValue] at computed
  have claims : read sample.value = Real.sqrt 2 ∧
      read sample.value * (-Real.sqrt 2) + 2 = 0 ∧
      (read sample.value)^2 - 1 - 1 = 0 ∧ 1 < read sample.value ∧ read sample.value < 2 := by
    dsimp only [matrix, RealFormula.QF.toProp, RealFormula.Atom.toProp,
      RealFormula.Cmp.toProp] at meaning
    unfold RealFormula.Poly.eval at meaning
    simp_rw [← HexMvPolyTheory.eval₂_toMvPolynomial] at meaning
    simpa [HexMvPolyTheory.toMvPolynomial_X, HexMvPolyTheory.toMvPolynomial_sub,
      HexMvPolyTheory.toMvPolynomial_add, HexMvPolyTheory.toMvPolynomial_mul,
      HexMvPolyTheory.toMvPolynomial_pow, HexMvPolyTheory.toMvPolynomial_one,
      RealFormula.append, source, SourceSelectionConformance.source,
      sub_eq_zero, sub_pos, sub_lt_zero] using meaning
  exact ⟨read sample.value, claims.1, claims.2.1, claims.2.2.1,
    claims.2.2.2.1, claims.2.2.2.2, guarded, computed⟩

theorem negated_truth : Samples.Row.eval (.and inputs.formula.lift (.not (.not matrix)))
    (NativeSpecialize.row context values sample.value (.and inputs.formula.lift (.not (.not matrix)))) =
      some true := by
  apply (Samples.Row.eval_true _ _ _ (NativeSpecialize.row_model model values sample.value _)).mpr
  have original := (Samples.Row.eval_true _ _ _
    (NativeSpecialize.row_model model values sample.value _)).mp truth
  exact ⟨original.1, not_not_intro original.2⟩

/-- A false universal is refuted through the same generated source identities,
at one reader satisfying the two original nonzero guards. -/
theorem counterexample : ¬ ∀ x : ℝ, ¬ matrix.toProp (RealFormula.append source x) := by
  have result := inputs.not_forall context following values source authenticated
    (by
      intro i inherited
      have impossible : (false : Bool) = true := (inherited_empty i).symm.trans inherited
      cases impossible)
    sample.value (.not matrix) [divisor,computedDivisor]
    (by
      intro a member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact nonzero
      · exact computed_nonzero) negated_truth
  exact result.1

def swapped : Fin 4 → context.Value := fun i =>
  if i = 1 then values 3 else if i = 3 then values 1 else values i

#guard Samples.Row.eval (.and inputs.formula.lift matrix)
  (NativeSpecialize.row context values sample.value (.and inputs.formula.lift matrix)) == some true

#guard Samples.Row.eval (.and inputs.formula.lift matrix)
  (NativeSpecialize.row context swapped sample.value (.and inputs.formula.lift matrix)) == some false

run_meta do
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies #[``witness]
  for law in #[``SourceSelection.exists_real,``SourceSelection.unique,
      ``NativeSources.true_real,``truth,``nonzero,``computed_nonzero,``reader,``FieldSelection.authenticated,``source_eq,
      ``Coefficients.ofField_gen] do
    unless dependencies.contains law do
      Lean.throwError m!"native tuple omitted its selected/source/row/guard law: {law}"
  let negative ← Hex.RCF.ProofEvidence.projectDependencies #[``counterexample]
  unless negative.contains ``SourceSelection.not_forall && negative.contains ``NativeSources.not_forall do
    Lean.throwError "native universal counterexample omitted its generated-authentication API"
  let axioms ← Lean.collectAxioms ``witness
  unless axioms.size == 3 && axioms.all
      (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
    Lean.throwError m!"native tuple has unexpected axioms: {axioms}"

end Hex.RCF.SourceSelectionNative
