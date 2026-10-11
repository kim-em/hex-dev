/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.NativeSamples
import HexRCF.ProofEvidence
import HexRCF.Tactic
import HexRCF.SelectedRoot.Data
import HexRCF.SelectedRoot.Upper
import HexRCF.SelectedRoot.CatalogSource
import HexRealClosure.SharedPresentation
import HexRealClosure.Sample
import HexRCF.RealCoefficients.NativeSpecialize
/-! Oracle: independently stated selected-root facts and expected sign words;
mode: always. Covers actual coefficient conversion, shared atom order, root
sections, repeated/zero atoms, leading cancellation and half-open guard atoms.
Native guards are computational observations; the exact row theorems and their
complete axiom inventories are separate ordinary-kernel evidence. -/
namespace Hex.RCF.RealCoefficients.NativeSamplesConformance
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.RealFormula
open Hex.RCF.RealCoefficients
open scoped HexMvPolyMathlib
def sample : Tower.Sample Hex.RCF.SelectedRootTests.Data.base :=
  Tower.Sample.section _ Hex.RCF.SelectedRootTests.Data.lower
noncomputable def conversion := Classical.choose
  (Tower.Sample.section_correct Hex.RCF.SelectedRootTests.Data.lower
    Hex.RCF.SelectedRootTests.Data.rational)
theorem point : conversion.target.value sample.value = Hex.RCF.SelectedRootTests.Data.selectedReal :=
  (Classical.choose_spec (Tower.Sample.section_correct
    Hex.RCF.SelectedRootTests.Data.lower Hex.RCF.SelectedRootTests.Data.rational)).2.2

def values : Fin 2 → Hex.RCF.SelectedRootTests.Data.base.Value := fun _ => 2
def formula : RealFormula.QF 3 :=
  let c : RealFormula.Poly 3 := MvPoly.X 0
  let d : RealFormula.Poly 3 := MvPoly.X 1
  let x : RealFormula.Poly 3 := MvPoly.X 2
  let p := x ^ 2 - c
  .and (.atom ⟨p, .eq⟩) (.and (.atom ⟨p ^ 2, .ge⟩)
    (.and (.atom ⟨0, .eq⟩) (.and (.atom ⟨(c-d)*x^4+x, .gt⟩)
      (.and (.atom ⟨1-x, .lt⟩) (.atom ⟨x-2, .le⟩)))))

theorem row_converted :
    sample.signs (RepresentationSpecialize.prepare values formula) =
    NativeSpecialize.row sample.input.context (sample.input.value ∘ values) sample.value formula :=
  NativeSamples.row_converted Hex.RCF.SelectedRootTests.Data.rational sample conversion
    values formula

/-- info: 'Hex.RCF.RealCoefficients.NativeSamplesConformance.row_converted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms row_converted
theorem original_row : sample.signs (RepresentationSpecialize.prepare values formula) =
    [0, 0, 0, 1, -1, -1] := by
  rw [Tower.Sample.signs_correct sample Hex.RCF.SelectedRootTests.Data.rational conversion]
  have evaluations := congrArg (List.map (fun x : ℝ => (SignType.sign x : Int)))
    (RepresentationSpecialize.prepare_eval Hex.RCF.SelectedRootTests.Data.rational.value
      Hex.RCF.SelectedRootTests.Data.rational.zero_iff Hex.RCF.SelectedRootTests.Data.rational.one
      Hex.RCF.SelectedRootTests.Data.rational.add Hex.RCF.SelectedRootTests.Data.rational.mul
      Hex.RCF.SelectedRootTests.Data.rational.nat Hex.RCF.SelectedRootTests.Data.rational.neg
      values formula (conversion.target.value sample.value))
  simp only [List.map_map, Function.comp_def, RepresentationSpecialize.evaluate] at evaluations
  rw [evaluations, point]
  have square := Hex.RCF.SelectedRootTests.Data.selectedFacts.1
  have above := Hex.RCF.SelectedRootTests.Data.selectedFacts.2.1
  have below := Hex.RCF.SelectedRootTests.Data.selectedFacts.2.2
  dsimp only [formula, RealFormula.QF.polys, RealFormula.QF.polys.go, RealFormula.Poly.eval]
  simp_rw [← HexMvPolyMathlib.eval₂_toMvPolynomial]
  simp [HexMvPolyMathlib.toMvPolynomial_X, HexMvPolyMathlib.toMvPolynomial_sub,
    HexMvPolyMathlib.toMvPolynomial_add, HexMvPolyMathlib.toMvPolynomial_mul,
    HexMvPolyMathlib.toMvPolynomial_pow, HexMvPolyMathlib.toMvPolynomial_one,
    HexMvPolyMathlib.toMvPolynomial_zero, RealFormula.append, values,
    square,
    show (2 : RealFormula.Poly 3) = MvPoly.C 2 from rfl,
    _root_.sign_pos (show 0 < Hex.RCF.SelectedRootTests.Data.selectedReal by linarith),
    _root_.sign_neg (show 1 - Hex.RCF.SelectedRootTests.Data.selectedReal < 0 by linarith),
    _root_.sign_neg (show Hex.RCF.SelectedRootTests.Data.selectedReal - 2 < 0 by linarith)]
/-- The computed sample conversion preserves the six original atom positions. -/
theorem native_row :
    NativeSpecialize.row sample.input.context (sample.input.value ∘ values) sample.value formula =
      [0, 0, 0, 1, -1, -1] := row_converted.symm.trans original_row

/-- info: 'Hex.RCF.RealCoefficients.NativeSamplesConformance.native_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms native_row

#guard sample.signs (RepresentationSpecialize.prepare values formula) == [0, 0, 0, 1, -1, -1]
#guard NativeSpecialize.row sample.input.context (sample.input.value ∘ values)
  sample.value formula == [0, 0, 0, 1, -1, -1]

/-- A zero atom stays present; an empty traversal has no signs. -/
theorem empty_row :
    NativeSpecialize.row sample.input.context (sample.input.value ∘ values)
      sample.value (.tt : RealFormula.QF 3) = [] := by
  rw [← NativeSamples.row_converted Hex.RCF.SelectedRootTests.Data.rational sample conversion]
  rfl

def wrongValues : Fin 2 → Hex.RCF.SelectedRootTests.Data.base.Value := fun _ => -2
theorem wrong_row : sample.signs (RepresentationSpecialize.prepare wrongValues formula) =
    [1, 1, 0, 1, -1, -1] := by
  rw [Tower.Sample.signs_correct sample Hex.RCF.SelectedRootTests.Data.rational conversion]
  have evaluations := congrArg (List.map (fun x : ℝ => (SignType.sign x : Int)))
    (RepresentationSpecialize.prepare_eval Hex.RCF.SelectedRootTests.Data.rational.value
      Hex.RCF.SelectedRootTests.Data.rational.zero_iff Hex.RCF.SelectedRootTests.Data.rational.one
      Hex.RCF.SelectedRootTests.Data.rational.add Hex.RCF.SelectedRootTests.Data.rational.mul
      Hex.RCF.SelectedRootTests.Data.rational.nat Hex.RCF.SelectedRootTests.Data.rational.neg
      wrongValues formula (conversion.target.value sample.value))
  simp only [List.map_map, Function.comp_def, RepresentationSpecialize.evaluate] at evaluations
  rw [evaluations, point]
  have square := Hex.RCF.SelectedRootTests.Data.selectedFacts.1
  have above := Hex.RCF.SelectedRootTests.Data.selectedFacts.2.1
  have below := Hex.RCF.SelectedRootTests.Data.selectedFacts.2.2
  dsimp only [formula, RealFormula.QF.polys, RealFormula.QF.polys.go, RealFormula.Poly.eval]
  simp_rw [← HexMvPolyMathlib.eval₂_toMvPolynomial]
  simp [HexMvPolyMathlib.toMvPolynomial_X, HexMvPolyMathlib.toMvPolynomial_sub,
    HexMvPolyMathlib.toMvPolynomial_add, HexMvPolyMathlib.toMvPolynomial_mul,
    HexMvPolyMathlib.toMvPolynomial_pow, HexMvPolyMathlib.toMvPolynomial_one,
    HexMvPolyMathlib.toMvPolynomial_zero, RealFormula.append, wrongValues,
    square,
    show (2 : RealFormula.Poly 3) = MvPoly.C 2 from rfl,
    _root_.sign_pos (show 0 < Hex.RCF.SelectedRootTests.Data.selectedReal by linarith),
    _root_.sign_neg (show 1 - Hex.RCF.SelectedRootTests.Data.selectedReal < 0 by linarith),
    _root_.sign_neg (show Hex.RCF.SelectedRootTests.Data.selectedReal - 2 < 0 by linarith)]
  erw [Hex.RCF.SelectedRootTests.Data.rationalNegativeTwo]
  norm_num

/-- Changing the source coordinates changes the row, even at the same
selected root and in the same converted context. -/
theorem changed_row :
    NativeSpecialize.row sample.input.context (sample.input.value ∘ wrongValues)
      sample.value formula ≠
    NativeSpecialize.row sample.input.context (sample.input.value ∘ values)
      sample.value formula := by
  rw [← NativeSamples.row_converted Hex.RCF.SelectedRootTests.Data.rational sample conversion,
    wrong_row, native_row]
  decide +kernel

#guard sample.signs (RepresentationSpecialize.prepare wrongValues formula) == [1, 1, 0, 1, -1, -1]
#guard NativeSpecialize.row sample.input.context (sample.input.value ∘ wrongValues)
  sample.value formula == [1, 1, 0, 1, -1, -1]
#guard NativeSpecialize.row sample.input.context (sample.input.value ∘ values)
  sample.value (.tt : RealFormula.QF 3) == []

/-- info: 'Hex.RCF.RealCoefficients.NativeSamplesConformance.empty_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms empty_row
/-- info: 'Hex.RCF.RealCoefficients.NativeSamplesConformance.changed_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms changed_row

/-- The actual converted atom family has the original normalized sizes. -/
theorem sizes :
    (RepresentationSpecialize.prepare (sample.input.value ∘ values) formula).map (fun p => p.size) =
      (RepresentationSpecialize.prepare values formula).map (fun p => p.size) := by
  unfold RepresentationSpecialize.prepare
  simp only [List.map_map]
  apply List.map_congr_left
  intro q _
  exact NativeSamples.size_converted Hex.RCF.SelectedRootTests.Data.rational sample conversion values q

/-- The source family’s exact normalized size vector is ordinary-kernel checked. -/
theorem source_sizes : (RepresentationSpecialize.prepare values formula).map (fun p => p.size) =
    [3, 5, 0, 2, 2, 2] := by decide +kernel

def constants : RealFormula.QF 3 :=
  .and (.atom ⟨0, .eq⟩) (.and (.atom ⟨2, .gt⟩) (.atom ⟨1, .le⟩))

/-- A zero atom and nonzero constants stay distinct after conversion. -/
theorem constant_sizes :
    (RepresentationSpecialize.prepare (sample.input.value ∘ values) constants).map (fun p => p.size) =
      (RepresentationSpecialize.prepare values constants).map (fun p => p.size) := by
  unfold RepresentationSpecialize.prepare
  simp only [List.map_map]
  apply List.map_congr_left
  intro q _
  exact NativeSamples.size_converted Hex.RCF.SelectedRootTests.Data.rational sample conversion values q

/-- Zero and the two nonzero constants have independently checked sizes. -/
theorem source_constants : (RepresentationSpecialize.prepare values constants).map (fun p => p.size) =
    [0, 1, 1] := by decide +kernel

/-- info: 'Hex.RCF.RealCoefficients.NativeSamplesConformance.source_sizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_sizes
/-- info: 'Hex.RCF.RealCoefficients.NativeSamplesConformance.source_constants' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source_constants

run_meta do
  for name in #[``source_sizes, ``source_constants] do
    let _ ← Hex.RCF.checkProof name (← Lean.Meta.inferType (Lean.mkConst name)) (Lean.mkConst name)
    let axioms ← Lean.collectAxioms name
    unless axioms.size == 3 && axioms.all
        (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
      Lean.throwError "source size word has an unexpected complete axiom inventory"

#guard (RepresentationSpecialize.prepare values formula).map (fun p => p.size) == [3, 5, 0, 2, 2, 2]
#guard (RepresentationSpecialize.prepare (sample.input.value ∘ values) formula).map
  (fun p => p.size) == [3, 5, 0, 2, 2, 2]
#guard (RepresentationSpecialize.prepare values constants).map (fun p => p.size) == [0, 1, 1]
#guard (RepresentationSpecialize.prepare (sample.input.value ∘ values) constants).map
  (fun p => p.size) == [0, 1, 1]

/-- info: 'Hex.RCF.RealCoefficients.NativeSamplesConformance.sizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sizes
/-- info: 'Hex.RCF.RealCoefficients.NativeSamplesConformance.constant_sizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms constant_sizes

run_meta do
  for name in #[``native_row, ``empty_row, ``changed_row, ``sizes, ``constant_sizes] do
    let proof := Lean.mkConst name
    let target ← Lean.Meta.inferType proof
    let _ ← Hex.RCF.checkProof name target proof
    let law := if name == ``sizes || name == ``constant_sizes then ``NativeSamples.size_converted
      else ``NativeSamples.row_converted
    unless ← Hex.RCF.ProofEvidence.contains name
        (fun e => e.isConstOf law) do
      Lean.throwError "sample regression lost the actual coefficient-conversion law"
    let axioms ← Lean.collectAxioms name
    unless axioms.size == 3 && axioms.all
        (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
      Lean.throwError "sample regression has an unexpected complete axiom inventory"

namespace Nested
open Hex.RCF.SelectedRootTests

/-- The upper section has an algebraic coefficient from the lower section. -/
def sample : Tower.Sample Data.parent := Tower.Sample.section _ Upper.root
noncomputable def conversion := Classical.choose
  (Tower.Sample.section_correct Upper.root Data.original)

theorem coefficient_fixed :
    conversion.target.value (sample.input.value Data.alpha) = Real.sqrt 2 :=
  (conversion.value _).trans Data.alpha_value

theorem row_converted :
    sample.signs (RepresentationSpecialize.prepare Upper.values Upper.schema) =
      NativeSpecialize.row sample.input.context (sample.input.value ∘ Upper.values)
        sample.value Upper.schema :=
  NativeSamples.row_converted Data.original sample conversion Upper.values Upper.schema

theorem sizes :
    (RepresentationSpecialize.prepare (sample.input.value ∘ Upper.values) Upper.schema).map
        (fun p => p.size) =
      (RepresentationSpecialize.prepare Upper.values Upper.schema).map (fun p => p.size) := by
  unfold RepresentationSpecialize.prepare
  simp only [List.map_map]
  apply List.map_congr_left
  intro q _
  exact NativeSamples.size_converted Data.original sample conversion Upper.values q

theorem point : conversion.target.value sample.value = CatalogSource.selected.denote Data.original :=
  (Classical.choose_spec (Tower.Sample.section_correct Upper.root Data.original)).2.2.trans
    (CatalogSource.selected.denote_selection Data.original).symm

theorem source_row : sample.signs (RepresentationSpecialize.prepare Upper.values Upper.schema) =
    [0, 1, -1] := by
  rw [Tower.Sample.signs_correct sample Data.original conversion]
  have evaluations := congrArg (List.map (fun x : ℝ => (SignType.sign x : Int)))
    (RepresentationSpecialize.prepare_eval Data.original.value Data.original.zero_iff
      Data.original.one Data.original.add Data.original.mul Data.original.nat Data.original.neg
      Upper.values Upper.schema (conversion.target.value sample.value))
  simp only [List.map_map, Function.comp_def, RepresentationSpecialize.evaluate] at evaluations
  rw [evaluations, point]
  have square := CatalogSource.source.1
  have above := CatalogSource.source.2.1
  have below := CatalogSource.source.2.2
  dsimp only [Upper.schema, RealFormula.QF.polys, RealFormula.QF.polys.go, RealFormula.Poly.eval]
  simp_rw [← HexMvPolyMathlib.eval₂_toMvPolynomial]
  simp [HexMvPolyMathlib.toMvPolynomial_X, HexMvPolyMathlib.toMvPolynomial_sub,
    HexMvPolyMathlib.toMvPolynomial_pow, HexMvPolyMathlib.toMvPolynomial_one,
    RealFormula.append, Upper.values, Data.alpha_value, square,
    show (2 : RealFormula.Poly 2) = MvPoly.C 2 from rfl,
    _root_.sign_pos (show 0 < CatalogSource.selected.denote Data.original - 1 by linarith),
    _root_.sign_neg (show CatalogSource.selected.denote Data.original - 2 < 0 by linarith)]

theorem native_row : NativeSpecialize.row sample.input.context
    (sample.input.value ∘ Upper.values) sample.value Upper.schema = [0, 1, -1] :=
  row_converted.symm.trans source_row

def wrongValues : Fin 1 → Data.parent.Value := fun _ => -Data.alpha

theorem wrong_row : sample.signs (RepresentationSpecialize.prepare wrongValues Upper.schema) =
    [1, 1, -1] := by
  rw [Tower.Sample.signs_correct sample Data.original conversion]
  have evaluations := congrArg (List.map (fun x : ℝ => (SignType.sign x : Int)))
    (RepresentationSpecialize.prepare_eval Data.original.value Data.original.zero_iff
      Data.original.one Data.original.add Data.original.mul Data.original.nat Data.original.neg
      wrongValues Upper.schema (conversion.target.value sample.value))
  simp only [List.map_map, Function.comp_def, RepresentationSpecialize.evaluate] at evaluations
  rw [evaluations, point]
  have square := CatalogSource.source.1
  have above := CatalogSource.source.2.1
  have below := CatalogSource.source.2.2
  have positive : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  dsimp only [Upper.schema, RealFormula.QF.polys, RealFormula.QF.polys.go, RealFormula.Poly.eval]
  simp_rw [← HexMvPolyMathlib.eval₂_toMvPolynomial]
  simp [HexMvPolyMathlib.toMvPolynomial_X, HexMvPolyMathlib.toMvPolynomial_sub,
    HexMvPolyMathlib.toMvPolynomial_pow, HexMvPolyMathlib.toMvPolynomial_one,
    RealFormula.append, wrongValues, square,
    show (2 : RealFormula.Poly 2) = MvPoly.C 2 from rfl,
    _root_.sign_pos (show 0 < CatalogSource.selected.denote Data.original - 1 by linarith),
    _root_.sign_neg (show CatalogSource.selected.denote Data.original - 2 < 0 by linarith)]

  erw [Data.original.neg, Data.alpha_value]
  simp

theorem wrong_native : NativeSpecialize.row sample.input.context
    (sample.input.value ∘ wrongValues) sample.value Upper.schema = [1, 1, -1] :=
  (NativeSamples.row_converted Data.original sample conversion wrongValues Upper.schema).symm.trans wrong_row


#guard sample.signs (RepresentationSpecialize.prepare Upper.values Upper.schema) == [0, 1, -1]
#guard NativeSpecialize.row sample.input.context (sample.input.value ∘ Upper.values)
  sample.value Upper.schema == [0, 1, -1]

/-- info: 'Hex.RCF.RealCoefficients.NativeSamplesConformance.Nested.coefficient_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coefficient_fixed
/-- info: 'Hex.RCF.RealCoefficients.NativeSamplesConformance.Nested.row_converted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms row_converted
/-- info: 'Hex.RCF.RealCoefficients.NativeSamplesConformance.Nested.sizes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sizes

run_meta do
  for (name, law) in #[(``coefficient_fixed, ``Data.alpha_value),
      (``row_converted, ``NativeSamples.row_converted), (``sizes, ``NativeSamples.size_converted)] do
    let proof := Lean.mkConst name
    let target ← Lean.Meta.inferType proof
    let _ ← Hex.RCF.checkProof name target proof
    unless ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf law) do
      Lean.throwError "nested sample lost its actual conversion or selected embedding law"
    let axioms ← Lean.collectAxioms name
    unless axioms.size == 3 && axioms.all
        (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
      Lean.throwError "nested sample has an unexpected complete axiom inventory"
#guard sample.signs (RepresentationSpecialize.prepare wrongValues Upper.schema) == [1, 1, -1]
#guard NativeSpecialize.row sample.input.context (sample.input.value ∘ wrongValues)
  sample.value Upper.schema == [1, 1, -1]

/-- info: 'Hex.RCF.RealCoefficients.NativeSamplesConformance.Nested.native_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms native_row
/-- info: 'Hex.RCF.RealCoefficients.NativeSamplesConformance.Nested.wrong_native' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms wrong_native

run_meta do
  for name in #[``native_row, ``wrong_native] do
    let _ ← Hex.RCF.checkProof name (← Lean.Meta.inferType (Lean.mkConst name)) (Lean.mkConst name)
    for law in #[``NativeSamples.row_converted, ``CatalogSource.source] do
      unless ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf law) do
        Lean.throwError "nested word omitted conversion or selected-root source evidence"
    let axioms ← Lean.collectAxioms name
    unless axioms.size == 3 && axioms.all
        (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
      Lean.throwError "nested word has an unexpected complete axiom inventory"
end Nested

namespace Point
open Hex.RCF.SelectedRootTests

private theorem origin_eq : sample.input.context.origin =
    Origin.pack (BaseContext.rational Data.registry) (.root Data.lower .nil) rfl :=
  Context.origin_adjoin_base _ _

private noncomputable def history : (BaseContext.rational Data.registry).chain.Realization Data.registry := by
  change (BaseContext.Chain.real (.base (registry := Data.registry))).Realization Data.registry
  exact .real .base (BaseContext.RealChain.interpretBase Data.registry) .base

noncomputable def following : sample.input.context.origin.base.Realization := by
  rw [origin_eq]
  exact history

theorem coordinate : sample.input.context.origin.RealValue following (sample.input.value 2) 2 := by
  simp only [following]
  apply (Origin.realValue_pack _ _ _ _ _).mpr
  refine ⟨(2 : Data.base.Value), rfl, ?_⟩
  change (BaseContext.RealChain.interpretBase Data.registry).hom (2 : Rat) = 2
  norm_num [BaseContext.RealChain.interpretBase, BaseContext.RealContext.Interpretation.rational]

theorem true_row : Samples.Row.eval formula
    (sample.signs (RepresentationSpecialize.prepare values formula)) = some true := by
  rw [row_converted, native_row]
  decide +kernel

/-- Actual inherited coordinates and an original parent guard at the section. -/
theorem true_real : ∃ x : ℝ,
    formula.toProp (RealFormula.append (fun _ : Fin 2 => 2) x) ∧ (2 : ℝ) ≠ 0 := by
  obtain ⟨read, domain, closed, negative, present, sizes, truth, guards, fixed⟩ :=
    NativeSamples.true_real Data.rational sample conversion following values (fun _ => 2)
      (fun _ => coordinate) formula [2] (by
        intro a ha
        have same : a = 2 := List.mem_singleton.mp ha
        subst a
        decide +kernel) true_row
  have guard := (guards (2 : Data.base.Value) (by simp)).2
  have two := (fixed _ _ coordinate).2
  rw [two] at guard
  exact ⟨read sample.value, truth, guard⟩

def falseFormula : RealFormula.QF 3 := .atom ⟨MvPoly.X 2 ^ 2 - MvPoly.X 0, .gt⟩

theorem false_native : NativeSpecialize.row sample.input.context
    (sample.input.value ∘ values) sample.value falseFormula = [0] := by
  have first := congrArg List.head? native_row
  simpa [NativeSpecialize.row, RepresentationSpecialize.prepare, formula, falseFormula,
    RealFormula.QF.polys, RealFormula.QF.polys.go] using first

theorem false_row : Samples.Row.eval falseFormula
    (sample.signs (RepresentationSpecialize.prepare values falseFormula)) = some false := by
  rw [NativeSamples.row_converted Data.rational sample conversion, false_native]
  decide +kernel

theorem not_forall : ¬ ∀ x : ℝ, x ^ 2 > 2 := by
  have failure := NativeSamples.not_forall Data.rational sample conversion following values
    (fun _ => 2) (fun _ => coordinate) falseFormula false_row
  intro all
  apply failure
  intro x
  dsimp only [falseFormula, RealFormula.QF.toProp, RealFormula.Atom.toProp, RealFormula.Cmp.toProp]
  unfold RealFormula.Poly.eval
  rw [← HexMvPolyMathlib.eval₂_toMvPolynomial]
  simpa [HexMvPolyMathlib.toMvPolynomial_X, HexMvPolyMathlib.toMvPolynomial_pow,
    HexMvPolyMathlib.toMvPolynomial_sub, RealFormula.append] using sub_pos.mpr (all x)


/-- info: 'Hex.RCF.RealCoefficients.NativeSamplesConformance.Point.coordinate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms coordinate
/-- info: 'Hex.RCF.RealCoefficients.NativeSamplesConformance.Point.true_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms true_real
/-- info: 'Hex.RCF.RealCoefficients.NativeSamplesConformance.Point.not_forall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms not_forall

run_meta do
  for (name, laws) in #[(``coordinate, #[``Origin.realValue_pack]),
      (``true_real, #[``NativeSamples.true_real, ``coordinate, ``true_row]),
      (``not_forall, #[``NativeSamples.not_forall, ``coordinate, ``false_row])] do
    let _ ← Hex.RCF.checkProof name (← Lean.Meta.inferType (Lean.mkConst name)) (Lean.mkConst name)
    for law in laws do
      unless ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf law) do
        Lean.throwError "point consumer omitted an actual premise or point API"
    let axioms ← Lean.collectAxioms name
    unless axioms.size == 3 && axioms.all
        (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
      Lean.throwError "point consumer has an unexpected complete axiom inventory"
end Point

end Hex.RCF.RealCoefficients.NativeSamplesConformance

/-- info: 'Hex.RCF.RealCoefficients.NativeSamples.row_converted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.NativeSamples.row_converted
/-- info: 'Hex.RCF.RealCoefficients.NativeSamples.true_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.NativeSamples.true_real
/-- info: 'Hex.RCF.RealCoefficients.NativeSamples.not_forall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.NativeSamples.not_forall
/-- info: 'Hex.RCF.RealCoefficients.RepresentationSpecialize.polynomial_eval₂' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.RepresentationSpecialize.polynomial_eval₂


/-- info: 'Hex.RCF.RealCoefficients.NativeSamples.sign_converted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.NativeSamples.sign_converted

/-- info: 'Hex.RCF.RealCoefficients.NativeSamples.polynomial_converted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.NativeSamples.polynomial_converted

/-- info: 'Hex.RCF.RealCoefficients.NativeSamples.degree_converted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.NativeSamples.degree_converted

/-- info: 'Hex.RCF.RealCoefficients.NativeSamples.size_converted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RCF.RealCoefficients.NativeSamples.size_converted
