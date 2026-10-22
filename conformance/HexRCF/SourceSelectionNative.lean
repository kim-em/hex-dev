/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.SourceSelectionConformance
public import HexRCF.FieldSelectionConformance
public import HexRCF.NativeSamplesConformance
public import HexRCF.RealCoefficients.FieldSelection

public section

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

abbrev coordinates := FieldSelectionConformance.coordinates

def inputs := FieldSelection.prepare SourceSelectionCases.root coordinates
noncomputable abbrev source := SourceSelectionConformance.source

theorem source_eq : FieldSelection.source SourceSelectionCases.root coordinates = source := by
  simpa only [source, SourceSelectionConformance.source, FieldSelectionConformance.source,
    FieldSelectionConformance.root] using FieldSelectionConformance.source_eq

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

def original : RealFormula.QF 4 :=
  let x : RealFormula.Poly 4 := MvPoly.X 3
  .and (.atom ⟨x + MvPoly.X 0, .eq⟩)
    (.and (.atom ⟨x * MvPoly.X 0 + MvPoly.X 1, .eq⟩)
      (.and (.atom ⟨x^2 - MvPoly.X 2 - 1, .eq⟩)
        (.and (.atom ⟨x - 1, .gt⟩) (.atom ⟨x - MvPoly.X 1, .lt⟩))))

def matrix : RealFormula.QF 5 := FieldSelection.matrix original

theorem original_matrix (x : ℝ) : matrix.toProp (RealFormula.append source x) ↔
    original.toProp (RealFormula.append (fun i : Fin 3 => source i.succ) x) := by
  have split : source = Fin.cases (source 0) (fun i : Fin 3 => source i.succ) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  rw [split]
  exact FieldSelection.matrix_correct original (source 0) _ x

theorem truth : Samples.Row.eval (.and inputs.formula.lift matrix)
    (NativeSpecialize.row context values sample.value (.and inputs.formula.lift matrix)) =
      some true := by
  apply (Samples.Row.eval_true _ _ _ (NativeSpecialize.row_model model values sample.value _)).mpr
  change inputs.formula.lift.toProp
    (RealFormula.append (model.value ∘ values) (model.value sample.value)) ∧
    matrix.toProp (RealFormula.append (model.value ∘ values) (model.value sample.value))
  rw [values_real, point]
  refine ⟨(inputs.formula.lift_correct _ _).mpr authenticated, ?_⟩
  apply (original_matrix _).mpr
  have above : 1 < Real.sqrt (2 : ℝ) := by
    rw [← Data.selectedSqrt]
    exact Data.selectedFacts.2.1
  have below : Real.sqrt (2 : ℝ) < 2 := by
    rw [← Data.selectedSqrt]
    exact Data.selectedFacts.2.2
  dsimp only [original, RealFormula.QF.toProp, RealFormula.Atom.toProp, RealFormula.Cmp.toProp]
  unfold RealFormula.Poly.eval
  simp_rw [← HexMvPolyTheory.eval₂_toMvPolynomial]
  norm_num [HexMvPolyTheory.toMvPolynomial_X, HexMvPolyTheory.toMvPolynomial_sub,
    HexMvPolyTheory.toMvPolynomial_add, HexMvPolyTheory.toMvPolynomial_mul,
    HexMvPolyTheory.toMvPolynomial_pow, HexMvPolyTheory.toMvPolynomial_one,
    RealFormula.append, source, SourceSelectionConformance.source,
    show (2 : RealFormula.Poly 4) = MvPoly.C 2 from rfl]
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

/-- Recover the original matrix at the very same finite reader. -/
theorem original_reader : ∃ read : context.Value → ℝ, ∃ domain : context.Value → Prop,
    Transport.Closed read domain ∧
    (∀ i, domain (values i) ∧ read (values i) = source i) ∧ domain sample.value ∧
    original.toProp (RealFormula.append (fun i : Fin 3 => source i.succ) (read sample.value)) ∧
    read divisor ≠ 0 ∧ read computedDivisor ≠ 0 := by
  obtain ⟨read,domain,closed,fixed,present,meaning,guarded,computed⟩ := reader
  exact ⟨read,domain,closed,fixed,present,(original_matrix _).mp meaning,guarded,computed⟩

private theorem tuple_first {α : Type} (a b c d : α) : (![a,b,c,d]) 0 = a := rfl
private theorem tuple_third {α : Type} (a b c d : α) : (![a,b,c,d]) 2 = c := rfl

theorem values_first : values 0 = sample.value :=
  tuple_first _ _ _ _

theorem values_third : values 2 = sample.input.value (2 : Data.base.Value) :=
  tuple_third _ _ _ _

/-- Readable closed projection of `original_reader`; the reader theorem
retains the coefficient and guard ties used by this proof. -/
theorem witness : ∃ x : ℝ, x = Real.sqrt 2 ∧ x * (-Real.sqrt 2) + 2 = 0 ∧
    x^2 - 1 - 1 = 0 ∧ 1 < x ∧ x < 2 ∧ 2-x ≠ 0 ∧ 1+Real.sqrt 2 ≠ 0 := by
  obtain ⟨read, domain, closed, fixed, present, meaning, guarded, computed⟩ := original_reader
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
    dsimp only [original, RealFormula.QF.toProp, RealFormula.Atom.toProp,
      RealFormula.Cmp.toProp] at meaning
    unfold RealFormula.Poly.eval at meaning
    simp_rw [← HexMvPolyTheory.eval₂_toMvPolynomial] at meaning
    simpa [HexMvPolyTheory.toMvPolynomial_X, HexMvPolyTheory.toMvPolynomial_sub,
      HexMvPolyTheory.toMvPolynomial_add, HexMvPolyTheory.toMvPolynomial_mul,
      HexMvPolyTheory.toMvPolynomial_pow, HexMvPolyTheory.toMvPolynomial_one,
      RealFormula.append, source, SourceSelectionConformance.source,
      ← sub_eq_add_neg, sub_eq_zero, sub_pos, sub_lt_zero] using meaning
  exact ⟨read sample.value, claims.1, claims.2.1, claims.2.2.1,
    claims.2.2.2.1, claims.2.2.2.2, guarded, computed⟩

def negativeMatrix : RealFormula.QF 5 :=
  .atom ⟨MvPoly.X 4 * MvPoly.X 1 + MvPoly.X 2,.ne⟩

theorem negative_meaning (x : ℝ) :
    negativeMatrix.toProp (RealFormula.append source x) ↔ x * (-Real.sqrt 2) + 2 ≠ 0 := by
  dsimp only [negativeMatrix, RealFormula.QF.toProp, RealFormula.Atom.toProp, RealFormula.Cmp.toProp]
  unfold RealFormula.Poly.eval
  simp_rw [← HexMvPolyTheory.eval₂_toMvPolynomial]
  simp [HexMvPolyTheory.toMvPolynomial_X, HexMvPolyTheory.toMvPolynomial_mul,
    HexMvPolyTheory.toMvPolynomial_add, RealFormula.append, source, SourceSelectionConformance.source]

theorem negated_truth : Samples.Row.eval (.and inputs.formula.lift (.not negativeMatrix))
    (NativeSpecialize.row context values sample.value (.and inputs.formula.lift (.not negativeMatrix))) =
      some true := by
  apply (Samples.Row.eval_true _ _ _ (NativeSpecialize.row_model model values sample.value _)).mpr
  change inputs.formula.lift.toProp
      (RealFormula.append (model.value ∘ values) (model.value sample.value)) ∧
    ¬ negativeMatrix.toProp (RealFormula.append (model.value ∘ values) (model.value sample.value))
  rw [values_real, point]
  refine ⟨(inputs.formula.lift_correct _ _).mpr authenticated, ?_⟩
  rw [negative_meaning]
  intro nonzero
  apply nonzero
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- A separately evaluated false universal retains both supplied guards at
its actual counterexample reader. -/
theorem counterexample : (¬ ∀ x : ℝ, x * (-Real.sqrt 2) + 2 ≠ 0) ∧
    ∃ read : context.Value → ℝ, ∃ domain : context.Value → Prop,
      Transport.Closed read domain ∧
      (∀ i, domain (values i) ∧ read (values i) = source i) ∧ domain sample.value ∧
      read sample.value * (-Real.sqrt 2) + 2 = 0 ∧
      (∀ a ∈ [divisor,computedDivisor], domain a ∧ read a ≠ 0) := by
  have result := inputs.not_forall context following values source authenticated
    (by
      intro i inherited
      have impossible : (false : Bool) = true := (inherited_empty i).symm.trans inherited
      cases impossible)
    sample.value negativeMatrix [divisor,computedDivisor]
    (by
      intro a member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact nonzero
      · exact computed_nonzero) negated_truth
  refine ⟨fun h => result.1 (fun x => (negative_meaning x).mpr (h x)), ?_⟩
  obtain ⟨read, domain, closed, fixed, present, negative, guarded⟩ := result.2
  refine ⟨read,domain,closed,fixed,present,?_,guarded⟩
  by_contra different
  exact negative ((negative_meaning _).mpr different)

theorem inherited_truth : Samples.Row.eval
    (.and SourceSelectionConformance.inputs.formula.lift matrix)
    (NativeSpecialize.row context values sample.value
      (.and SourceSelectionConformance.inputs.formula.lift matrix)) = some true := by
  apply (Samples.Row.eval_true _ _ _ (NativeSpecialize.row_model model values sample.value _)).mpr
  have previous := (Samples.Row.eval_true _ _ _
    (NativeSpecialize.row_model model values sample.value _)).mp truth
  rw [values_real] at previous
  change SourceSelectionConformance.inputs.formula.lift.toProp
    (RealFormula.append (model.value ∘ values) (model.value sample.value)) ∧ _
  rw [values_real]
  exact ⟨(SourceSelectionConformance.inputs.formula.lift_correct _ _).mpr
    SourceSelectionConformance.authenticated, previous.2⟩

/-- The inherited route consumes the actual origin identity for native 2. -/
theorem inherited_witness : ∃ x : ℝ, matrix.toProp (RealFormula.append source x) := by
  have inherited : context.origin.RealValue following (values 2) 2 := by
    rw [values_third]
    exact NativeSamplesConformance.Point.coordinate
  exact SourceSelectionConformance.realize context following values
    inherited sample.value matrix [] (by simp) inherited_truth

def swapped : Fin 4 → context.Value := fun i =>
  if i = 1 then values 3 else if i = 3 then values 1 else values i

/-- Selector rejection is independent of every user-matrix atom. -/
theorem swapped_selection : ¬ inputs.formula.toProp (model.value ∘ swapped) := by
  intro meaning
  have same := inputs.unique (model.value ∘ swapped) source
    (by intro i h; have impossible := (inherited_empty i).symm.trans h; cases impossible)
    meaning authenticated
  have wrong := congrFun same 1
  change model.value (swapped 1) = source 1 at wrong
  rw [swapped, ite_eq_left rfl] at wrong
  have actual := congrFun values_real 3
  change model.value (values 3) = 1 at actual
  change model.value (values 3) = -Real.sqrt 2 at wrong
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

#guard Samples.Row.eval inputs.formula.lift
  (NativeSpecialize.row context swapped sample.value inputs.formula.lift) == some false

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
