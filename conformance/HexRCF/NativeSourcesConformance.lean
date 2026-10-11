/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.NativeSources
import HexRCF.NativeSamplesConformance
import HexRealClosureMathlib.NativeRealization
import HexRealClosure.SharedPresentation

/-! Oracle: actual owner selected-root facts and independently stated complete
joint sign words; mode: always. The selection and source matrix are realized
together. Kernel proofs and inventories are separate from compiled controls.
Non-module imports expose the full private closure in the pinned toolchain. -/

namespace Hex.RCF.RealCoefficients.NativeSourcesConformance
open Hex Hex.RealClosure Hex.RealClosure.Tower
open Hex.RCF.RealCoefficients Hex.RCF.SelectedRootTests
open Hex.RealFormula
open scoped HexMvPolyMathlib

abbrev sample := NativeSamplesConformance.Nested.sample
abbrev context := sample.input.context

private theorem originBase : context.origin.base =
    BaseContext.PackedContext.pack (BaseContext.rational Data.registry) := by
  change (Data.parent.adjoin Upper.root).context.origin.base = _
  rw [Context.origin_adjoin, Origin.snoc_base, ← Data.parent_eq]
  change (Data.base.adjoin Data.lower).context.origin.base = _
  rw [Context.origin_adjoin, Origin.snoc_base]
  change (Context.base (BaseContext.rational Data.registry)).origin.base = _
  rw [Context.origin_base]
  rfl

noncomputable def following : context.origin.base.Realization := by
  rw [originBase]
  change (BaseContext.Chain.real (.base (registry := Data.registry))).Realization Data.registry
  exact .real .base (BaseContext.RealChain.interpretBase Data.registry) .base

def joint : RealFormula.QF 2 :=
  let c : RealFormula.Poly 2 := MvPoly.X 0
  .and (.atom ⟨c^2-2, .eq⟩) (.and (.atom ⟨c-1, .gt⟩)
    (.and (.atom ⟨c-2, .lt⟩) Upper.schema))

theorem source_row : sample.signs (RepresentationSpecialize.prepare Upper.values joint) =
    [0, 1, -1, 0, 1, -1] := by
  let conversion := NativeSamplesConformance.Nested.conversion
  rw [Tower.Sample.signs_correct sample Data.original conversion]
  have evaluations := congrArg (List.map (fun x : ℝ => (SignType.sign x : Int)))
    (RepresentationSpecialize.prepare_eval Data.original.value Data.original.zero_iff
      Data.original.one Data.original.add Data.original.mul Data.original.nat Data.original.neg
      Upper.values joint (conversion.target.value sample.value))
  simp only [List.map_map, Function.comp_def, RepresentationSpecialize.evaluate] at evaluations
  rw [evaluations, NativeSamplesConformance.Nested.point]
  have square := CatalogSource.source.1
  have above := CatalogSource.source.2.1
  have below := CatalogSource.source.2.2
  have lower : 1 < Real.sqrt (2 : ℝ) := by
    rw [← Data.selectedSqrt]
    exact Data.selectedFacts.2.1
  have upper : Real.sqrt (2 : ℝ) < 2 := by
    rw [← Data.selectedSqrt]
    exact Data.selectedFacts.2.2
  dsimp only [joint, Upper.schema, RealFormula.QF.polys, RealFormula.QF.polys.go, RealFormula.Poly.eval]
  simp_rw [← HexMvPolyMathlib.eval₂_toMvPolynomial]
  simp [HexMvPolyMathlib.toMvPolynomial_X, HexMvPolyMathlib.toMvPolynomial_sub,
    HexMvPolyMathlib.toMvPolynomial_pow, HexMvPolyMathlib.toMvPolynomial_one,
    RealFormula.append, Upper.values, Data.alpha_value, square,
    show (2 : RealFormula.Poly 2) = MvPoly.C 2 from rfl,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    _root_.sign_pos (show 0 < Real.sqrt 2 - 1 by linarith),
    _root_.sign_neg (show Real.sqrt 2 - 2 < 0 by linarith),
    _root_.sign_pos (show 0 < CatalogSource.selected.denote Data.original - 1 by linarith),
    _root_.sign_neg (show CatalogSource.selected.denote Data.original - 2 < 0 by linarith)]

def selection : RealFormula.QF 1 :=
  let c : RealFormula.Poly 1 := MvPoly.X 0
  .and (.atom ⟨c^2-2, .eq⟩) (.and (.atom ⟨c-1, .gt⟩) (.atom ⟨c-2, .lt⟩))

theorem selected (coefficients : Fin 1 → ℝ) (h : selection.toProp coefficients) :
    coefficients = fun _ => Real.sqrt 2 := by
  dsimp only [selection, RealFormula.QF.toProp, RealFormula.Atom.toProp,
    RealFormula.Cmp.toProp] at h
  unfold RealFormula.Poly.eval at h
  simp_rw [← HexMvPolyMathlib.eval₂_toMvPolynomial] at h
  have facts : (coefficients 0)^2=2 ∧ 1<coefficients 0 ∧ coefficients 0<2 := by
    simpa [HexMvPolyMathlib.toMvPolynomial_X, HexMvPolyMathlib.toMvPolynomial_sub,
      HexMvPolyMathlib.toMvPolynomial_pow, HexMvPolyMathlib.toMvPolynomial_one,
      show (2 : RealFormula.Poly 1)=MvPoly.C 2 from rfl, sub_eq_zero, sub_pos, sub_lt_zero] using h
  have same : coefficients 0 = Real.sqrt 2 := by
    nlinarith [facts.1, facts.2.1, Real.sq_sqrt (by norm_num : (0:ℝ)≤2), Real.sqrt_nonneg (2:ℝ)]
  funext i
  have index : i = 0 := Subsingleton.elim _ _
  simpa only [index] using same

theorem shape : (RealFormula.QF.and selection.lift Upper.schema).polys = joint.polys := by
  decide +kernel

theorem truth : Samples.Row.eval (RealFormula.QF.and selection.lift Upper.schema)
    (NativeSpecialize.row context
      (sample.input.value ∘ Upper.values) sample.value
      (RealFormula.QF.and selection.lift Upper.schema)) = some true := by
  have word := source_row
  rw [NativeSamples.row_converted Data.original sample
    NativeSamplesConformance.Nested.conversion] at word
  have same : NativeSpecialize.row context
      (sample.input.value ∘ Upper.values) sample.value
      (RealFormula.QF.and selection.lift Upper.schema) =
      NativeSpecialize.row context
      (sample.input.value ∘ Upper.values) sample.value
      joint := by
    simp only [NativeSpecialize.row, RepresentationSpecialize.prepare, shape]
  rw [same, word]
  decide +kernel

theorem source_real : ∃ x : ℝ, x^2 = Real.sqrt 2 ∧ 1<x ∧ x<2 := by
  obtain ⟨read, domain, closed, negative, fixed, present, sizes, meaning, guards, base⟩ :=
    NativeSources.true_real context following
      (sample.input.value ∘ Upper.values) (fun _ => Real.sqrt 2)
      selection (fun coefficients _ meaning => selected coefficients meaning) sample.value Upper.schema [] (by simp)
      truth
  refine ⟨read sample.value, ?_⟩
  dsimp only [Upper.schema, RealFormula.QF.toProp, RealFormula.Atom.toProp,
    RealFormula.Cmp.toProp] at meaning
  unfold RealFormula.Poly.eval at meaning
  simp_rw [← HexMvPolyMathlib.eval₂_toMvPolynomial] at meaning
  simpa [HexMvPolyMathlib.toMvPolynomial_X, HexMvPolyMathlib.toMvPolynomial_sub,
    HexMvPolyMathlib.toMvPolynomial_pow, HexMvPolyMathlib.toMvPolynomial_one,
    show (2 : RealFormula.Poly 2)=MvPoly.C 2 from rfl, RealFormula.append,
    sub_eq_zero, sub_pos, sub_lt_zero] using meaning

/-- info: 'Hex.RCF.RealCoefficients.NativeSourcesConformance.source_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_real


/-- The complete joint row changes at the same upper sample when the source
coefficient is changed to its negative conjugate. -/
theorem wrong_word : sample.signs
    (RepresentationSpecialize.prepare NativeSamplesConformance.Nested.wrongValues joint) =
    [0, -1, -1, 1, 1, -1] := by
  rw [Tower.Sample.signs_correct sample Data.original NativeSamplesConformance.Nested.conversion]
  have evaluations := congrArg (List.map (fun x : ℝ => (SignType.sign x : Int)))
    (RepresentationSpecialize.prepare_eval Data.original.value Data.original.zero_iff
      Data.original.one Data.original.add Data.original.mul Data.original.nat Data.original.neg
      NativeSamplesConformance.Nested.wrongValues joint
      (NativeSamplesConformance.Nested.conversion.target.value sample.value))
  simp only [List.map_map, Function.comp_def, RepresentationSpecialize.evaluate] at evaluations
  rw [evaluations, NativeSamplesConformance.Nested.point]
  have square := CatalogSource.source.1
  have above := CatalogSource.source.2.1
  have below := CatalogSource.source.2.2
  have positive : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  dsimp only [joint, Upper.schema, RealFormula.QF.polys, RealFormula.QF.polys.go, RealFormula.Poly.eval]
  simp_rw [← HexMvPolyMathlib.eval₂_toMvPolynomial]
  simp [HexMvPolyMathlib.toMvPolynomial_X, HexMvPolyMathlib.toMvPolynomial_sub,
    HexMvPolyMathlib.toMvPolynomial_pow, HexMvPolyMathlib.toMvPolynomial_one,
    RealFormula.append, NativeSamplesConformance.Nested.wrongValues, square,
    show (2 : RealFormula.Poly 2) = MvPoly.C 2 from rfl,
    _root_.sign_pos (show 0 < CatalogSource.selected.denote Data.original - 1 by linarith),
    _root_.sign_neg (show CatalogSource.selected.denote Data.original - 2 < 0 by linarith)]
  erw [Data.original.neg, Data.alpha_value]
  simp [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    _root_.sign_neg (show -Real.sqrt 2 - 1 < 0 by linarith),
    _root_.sign_neg (show -Real.sqrt 2 - 2 < 0 by linarith),
    _root_.sign_pos (show 0 < (Real.sqrt 2 + Real.sqrt 2) by linarith)]

theorem wrong_row : Samples.Row.eval (.and selection.lift Upper.schema)
    (NativeSpecialize.row context
      (sample.input.value ∘ NativeSamplesConformance.Nested.wrongValues)
      sample.value (.and selection.lift Upper.schema)) = some false := by
  have word := wrong_word
  rw [NativeSamples.row_converted Data.original sample
    NativeSamplesConformance.Nested.conversion] at word
  have same : NativeSpecialize.row context
      (sample.input.value ∘ NativeSamplesConformance.Nested.wrongValues)
      sample.value (.and selection.lift Upper.schema) =
      NativeSpecialize.row context
        (sample.input.value ∘ NativeSamplesConformance.Nested.wrongValues) sample.value joint := by
    simp only [NativeSpecialize.row, RepresentationSpecialize.prepare, shape]
  rw [same, word]
  decide +kernel

theorem wrong_conjugate : ¬ selection.toProp (fun _ => -Real.sqrt 2) := by
  intro wrong
  have same := congrFun (selected _ wrong) 0
  have positive : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  change -Real.sqrt 2 = Real.sqrt 2 at same
  linarith

def falseFormula : RealFormula.QF 2 := .atom ⟨MvPoly.X 1 ^ 2 - MvPoly.X 0, .gt⟩

theorem false_shape : (RealFormula.QF.and selection.lift (.not falseFormula)).polys =
    joint.polys.take 4 := by decide +kernel

theorem false_row : Samples.Row.eval (.and selection.lift (.not falseFormula))
    (NativeSpecialize.row context
      (sample.input.value ∘ Upper.values) sample.value
      (.and selection.lift (.not falseFormula))) = some true := by
  have word := source_row
  rw [NativeSamples.row_converted Data.original sample
    NativeSamplesConformance.Nested.conversion] at word
  have same : NativeSpecialize.row context
      (sample.input.value ∘ Upper.values) sample.value
      (.and selection.lift (.not falseFormula)) =
      (NativeSpecialize.row context
        (sample.input.value ∘ Upper.values) sample.value
        joint).take 4 := by
    simp only [NativeSpecialize.row, RepresentationSpecialize.prepare, false_shape, List.map_take]
  rw [same, word]
  decide +kernel

theorem divisor : context.sign
    (sample.input.value Data.alpha) ≠ 0 := by
  erw [NativeSamples.sign_converted Data.original sample
    NativeSamplesConformance.Nested.conversion Data.alpha, Data.original.sign, Data.alpha_value]
  have positive : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  simp [positive]

theorem guarded_counterexample :
    (¬ ∀ x : ℝ, falseFormula.toProp (RealFormula.append (fun _ => Real.sqrt 2) x)) ∧
    ∃ read : context.Value → ℝ, ∃ domain : context.Value → Prop,
      Transport.Closed read domain ∧
      (∀ i, domain ((sample.input.value ∘ Upper.values) i) ∧
        read ((sample.input.value ∘ Upper.values) i) = Real.sqrt 2) ∧
      domain sample.value ∧
      ¬ falseFormula.toProp (RealFormula.append (fun _ => Real.sqrt 2)
        (read sample.value)) ∧
      domain (sample.input.value Data.alpha) ∧
      read (sample.input.value Data.alpha) ≠ 0 := by
  have result := NativeSources.not_forall context following
    (sample.input.value ∘ Upper.values) (fun _ => Real.sqrt 2)
    selection (fun coefficients _ meaning => selected coefficients meaning) sample.value falseFormula
    [sample.input.value Data.alpha] (by
      intro a ha
      have same := List.mem_singleton.mp ha
      subst a
      exact divisor) false_row
  obtain ⟨counterexample, read, domain, closed, fixed, present, meaning, guard⟩ := result
  exact ⟨counterexample, read, domain, closed, fixed, present, meaning, guard _ (by simp)⟩

theorem zero_divisor : context.sign
    (sample.input.value (Data.alpha-Data.alpha)) = 0 := by
  erw [NativeSamples.sign_converted Data.original sample
    NativeSamplesConformance.Nested.conversion, Data.original.sign, Data.original.sub]
  simp

/-- info: 'Hex.RCF.RealCoefficients.NativeSourcesConformance.wrong_conjugate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_conjugate
/-- info: 'Hex.RCF.RealCoefficients.NativeSourcesConformance.guarded_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms guarded_counterexample
/-- info: 'Hex.RCF.RealCoefficients.NativeSourcesConformance.zero_divisor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms zero_divisor


/-- info: 'Hex.RCF.RealCoefficients.NativeSourcesConformance.source_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_row
/-- info: 'Hex.RCF.RealCoefficients.NativeSourcesConformance.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selected
/-- info: 'Hex.RCF.RealCoefficients.NativeSourcesConformance.truth' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms truth
/-- info: 'Hex.RCF.RealCoefficients.NativeSourcesConformance.wrong_word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_word
/-- info: 'Hex.RCF.RealCoefficients.NativeSourcesConformance.wrong_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_row
/-- info: 'Hex.RCF.RealCoefficients.NativeSourcesConformance.false_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms false_row
/-- info: 'Hex.RCF.RealCoefficients.NativeSourcesConformance.divisor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms divisor

run_meta do
  for (name, laws) in #[(``source_real, #[``NativeSources.true_real, ``selected, ``truth]),
      (``guarded_counterexample, #[``NativeSources.not_forall, ``selected, ``false_row, ``divisor]),
      (``wrong_row, #[``wrong_word, ``NativeSamples.row_converted]),
      (``zero_divisor, #[``NativeSamples.sign_converted, ``Tower.Model.sub])] do
    let _ ← Hex.RCF.checkProof name (← Lean.Meta.inferType (Lean.mkConst name)) (Lean.mkConst name)
    for law in laws do
      unless ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf law) do
        Lean.throwError "source authentication omitted a selection, row or original-guard law"
    let axioms ← Lean.collectAxioms name
    unless axioms.size == 3 && axioms.all
        (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
      Lean.throwError "source authentication has an unexpected complete axiom inventory"

#guard Samples.Row.eval (.and selection.lift Upper.schema)
  (NativeSpecialize.row context (sample.input.value ∘ Upper.values)
    sample.value (.and selection.lift Upper.schema)) == some true
#guard Samples.Row.eval (.and selection.lift Upper.schema)
  (NativeSpecialize.row context (sample.input.value ∘ NativeSamplesConformance.Nested.wrongValues)
    sample.value (.and selection.lift Upper.schema)) == some false
#guard Samples.Row.eval (.and selection.lift (.not falseFormula))
  (NativeSpecialize.row context (sample.input.value ∘ Upper.values)
    sample.value (.and selection.lift (.not falseFormula))) == some true

namespace Inherited
abbrev point := NativeSamplesConformance.sample
abbrev stage := point.input.context
noncomputable abbrev model : Tower.Model stage ℝ := NativeSamplesConformance.conversion.target
noncomputable abbrev history := NativeSamplesConformance.Point.following

def values : Fin 2 → stage.Value := fun i => if i = 0 then point.value else point.input.value 2
noncomputable def source : Fin 2 → ℝ := fun i => if i = 0 then Real.sqrt 2 else 2
def selection : RealFormula.QF 2 := NativeSourcesConformance.selection.lift
def matrix : RealFormula.QF 3 := .atom ⟨MvPoly.X 2 - MvPoly.X 0, .eq⟩
def joint : RealFormula.QF 3 :=
  let c : RealFormula.Poly 3 := MvPoly.X 0
  .and (.atom ⟨c^2-2, .eq⟩) (.and (.atom ⟨c-1, .gt⟩)
    (.and (.atom ⟨c-2, .lt⟩) matrix))
theorem shape : (RealFormula.QF.and selection.lift matrix).polys = joint.polys := by decide +kernel


theorem unique (coefficients : Fin 2 → ℝ)
    (known : ∀ i, stage.origin.RealValue history (values i) (source i) → coefficients i = source i)
    (meaning : selection.toProp coefficients) : coefficients = source := by
  have coordinate : stage.origin.RealValue history (values 1) (source 1) := by
    simpa [values, source] using NativeSamplesConformance.Point.coordinate
  have last := known 1 coordinate
  have same : RealFormula.append (fun _ : Fin 1 => coefficients 0) (coefficients 1) = coefficients := by
    funext i
    fin_cases i <;> rfl
  have first := NativeSourcesConformance.selected (fun _ : Fin 1 => coefficients 0)
    ((NativeSourcesConformance.selection.lift_correct _ _).mp (by
      rw [same]
      exact meaning))
  have first := congrFun first 0
  funext i
  fin_cases i
  · simpa [source] using first
  · simpa [source] using last

theorem word : NativeSpecialize.row stage values point.value (.and selection.lift matrix) =
    [0, 1, -1, 0] := by
  have mapped : NativeSpecialize.row stage values point.value (.and selection.lift matrix) =
      (RealFormula.QF.and selection.lift matrix).polys.map
        (fun q => (SignType.sign (q.eval
          (RealFormula.append (model.value ∘ values) (model.value point.value))) : Int)) := by
    unfold NativeSpecialize.row RepresentationSpecialize.prepare
    simp only [List.map_map]
    apply List.map_congr_left
    intro q _
    dsimp only [Function.comp_def]
    erw [model.sign, ← HexPolyMathlib.Interpret.eval_interpret model.value model.zero_iff model.add model.mul]
    change (SignType.sign (RepresentationSpecialize.evaluate model.value model.zero_iff
      (model.value point.value) (RepresentationSpecialize.polynomial values q)) : Int) = _
    rw [RepresentationSpecialize.polynomial_eval model.value model.zero_iff model.one
      model.add model.mul model.nat model.neg]
  have pointValue : model.value point.value = Real.sqrt 2 := by
    rw [NativeSamplesConformance.point, Data.selectedSqrt]
  have above : 1 < Real.sqrt (2 : ℝ) := by
    rw [← Data.selectedSqrt]
    exact Data.selectedFacts.2.1
  have below : Real.sqrt (2 : ℝ) < 2 := by
    rw [← Data.selectedSqrt]
    exact Data.selectedFacts.2.2
  rw [mapped, shape]
  dsimp only [joint, matrix, RealFormula.QF.polys, RealFormula.QF.polys.go, RealFormula.Poly.eval]
  simp_rw [← HexMvPolyMathlib.eval₂_toMvPolynomial]
  simp [HexMvPolyMathlib.toMvPolynomial_X, HexMvPolyMathlib.toMvPolynomial_sub,
    HexMvPolyMathlib.toMvPolynomial_pow, HexMvPolyMathlib.toMvPolynomial_one,
    RealFormula.append, values, pointValue, Function.comp_def,
    show (2 : RealFormula.Poly 3) = MvPoly.C 2 from rfl,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2),
    _root_.sign_pos (show 0 < Real.sqrt 2 - 1 by linarith),
    _root_.sign_neg (show Real.sqrt 2 - 2 < 0 by linarith)]

theorem truth : Samples.Row.eval (.and selection.lift matrix)
    (NativeSpecialize.row stage values point.value (.and selection.lift matrix)) = some true := by
  rw [word]
  decide +kernel

/-- The selection leaves the second coordinate unconstrained. The actual
inherited identity, not an added selection atom, identifies it as 2. -/
theorem reader : ∃ read : stage.Value → ℝ, ∃ domain : stage.Value → Prop,
    Transport.Closed read domain ∧
    read point.value = Real.sqrt 2 ∧ read (point.input.value 2) = 2 := by
  obtain ⟨read, domain, closed, negative, fixed, present, sizes, meaning, guards, base⟩ :=
    NativeSources.true_real stage history values source selection unique point.value matrix
      [] (by simp) truth
  have first := (fixed 0).2
  have last := (fixed 1).2
  exact ⟨read, domain, closed, by simpa [values, source] using first,
    by simpa [values, source] using last⟩
/-- info: 'Hex.RCF.RealCoefficients.NativeSourcesConformance.Inherited.unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms unique
/-- info: 'Hex.RCF.RealCoefficients.NativeSourcesConformance.Inherited.word' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms word
/-- info: 'Hex.RCF.RealCoefficients.NativeSourcesConformance.Inherited.reader' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms reader

run_meta do
  for (name, laws) in #[(``unique, #[``NativeSamplesConformance.Point.coordinate,
      ``NativeSourcesConformance.selected]), (``reader, #[``NativeSources.true_real, ``unique, ``truth])] do
    let _ ← Hex.RCF.checkProof name (← Lean.Meta.inferType (Lean.mkConst name)) (Lean.mkConst name)
    for law in laws do
      unless ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf law) do
        Lean.throwError "joint source identity omitted its inherited or selected source proof"
    let axioms ← Lean.collectAxioms name
    unless axioms.size == 3 && axioms.all
        (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
      Lean.throwError "joint source identity has an unexpected complete axiom inventory"
#guard Samples.Row.eval (.and selection.lift matrix)
  (NativeSpecialize.row stage values point.value (.and selection.lift matrix)) == some true

end Inherited

end Hex.RCF.RealCoefficients.NativeSourcesConformance

/-- info: 'Hex.RCF.RealCoefficients.NativeSources.true_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.NativeSources.true_real
/-- info: 'Hex.RCF.RealCoefficients.NativeSources.not_forall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.NativeSources.not_forall
