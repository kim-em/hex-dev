/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.SourceSelection
import HexRCF.SourceSelectionCases
import HexRCF.ProofEvidence
namespace Hex.RCF.SourceSelectionConformance
open Hex Hex.RealClosure Hex.RealFormula Hex.RCF.RealCoefficients
open scoped Hex

def inputs : SourceSelection 4 :=
  .coordinate (.inherited (.coordinate (.root .nil SourceSelectionCases.root)
    0 #p[0,-1])) 0 #p[-1,0,1]

noncomputable def source : Fin 4 → ℝ := ![Real.sqrt 2, -Real.sqrt 2, 2, 1]

/-- A polynomial coordinate may use a non-adjacent earlier generator. -/
theorem authenticated : inputs.formula.toProp source := by
  simp only [inputs, SourceSelection.formula, RealFormula.QF.lift,
    RealFormula.QF.rename_correct, RealFormula.QF.toProp]
  refine ⟨⟨⟨trivial, ?_⟩, ?_⟩, ?_⟩
  · apply (NativeSelection.identity SourceSelectionCases.root _ _).mpr
    simpa [source, Function.comp_def] using SourceSelectionCases.selected.symm
  · apply (NativeSelection.relation_correct _ _ _ _).mpr
    norm_num [realPoly, HexPolyTheory.Interpret.interpret_map, DensePoly.Interpret.map_ofCoeffs,
      HexPolyTheory.toPolynomial_ofCoeffs, Finset.sum_range_succ, ratCast,
      source, Function.comp_def]
  · apply (NativeSelection.relation_correct _ _ _ _).mpr
    norm_num [realPoly, HexPolyTheory.Interpret.interpret_map, DensePoly.Interpret.map_ofCoeffs,
      HexPolyTheory.toPolynomial_ofCoeffs, Finset.sum_range_succ, ratCast,
      source, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem inherited_exact (i : Fin 4) : inputs.isInherited i = true ↔ i = 2 := by
  revert i
  decide +kernel

/-- All four coordinates are fixed without a hand-written tuple uniqueness proof. -/
theorem unique (values : Fin 4 → ℝ) (fixed : values 2 = 2)
    (meaning : inputs.formula.toProp values) : values = source := by
  apply inputs.unique values source ?_ meaning authenticated
  intro i inherited
  have same := (inherited_exact i).mp inherited
  subst i
  exact fixed

/-- Correct equations at a different conjugate do not satisfy source selection. -/
theorem wrong_conjugate : ¬ inputs.formula.toProp ![-Real.sqrt 2,Real.sqrt 2,2,1] := by
  intro meaning
  have same := congrFun (unique _ rfl meaning) 0
  have positive := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  change -Real.sqrt 2 = Real.sqrt 2 at same
  linarith

/-- Swapping the computed coordinate and inherited value is also rejected. -/
theorem swapped : ¬ inputs.formula.toProp ![Real.sqrt 2,2,2,-Real.sqrt 2] := by
  intro meaning
  have same := congrFun (unique _ rfl meaning) 1
  change (2 : ℝ) = -Real.sqrt 2 at same
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

/-- The generated plan composes with the actual finite reader at arbitrary
native depth. Row truth remains checked input, not a compiled Boolean oracle. -/
theorem realize {registry : BaseContext.Registry} (context : Tower.Context registry)
    (following : context.origin.base.Realization) (values : Fin 4 → context.Value)
    (fixed : context.origin.RealValue following (values 2) 2)
    (sample : context.Value) (matrix : RealFormula.QF 5) (guards : List context.Value)
    (nonzero : ∀ a ∈ guards, context.sign a ≠ 0)
    (truth : Samples.Row.eval (.and inputs.formula.lift matrix)
      (NativeSpecialize.row context values sample (.and inputs.formula.lift matrix)) = some true) :
    ∃ x : ℝ, matrix.toProp (RealFormula.append source x) := by
  obtain ⟨read, domain, closed, identified, present, meaning, guarded⟩ :=
    inputs.exists_real context following values source authenticated (by
      intro i inherited
      have same := (inherited_exact i).mp inherited
      subst i
      exact fixed) sample matrix guards nonzero truth
  exact ⟨read sample, meaning⟩

run_meta do
  for name in #[``authenticated,``unique,``wrong_conjugate,``swapped,``realize,
      ``SourceSelection.unique,``SourceSelection.exists_real] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
      Lean.throwError m!"source selection has unexpected axioms: {name}: {axioms}"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies #[``realize]
  for law in #[``SourceSelection.exists_real,``SourceSelection.unique,``NativeSources.true_real] do
    unless dependencies.contains law do
      Lean.throwError m!"source selection omitted its shared or finite-realization law: {law}"

end Hex.RCF.SourceSelectionConformance
