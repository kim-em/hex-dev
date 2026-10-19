/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.SourceSelection
public import HexRCF.SourceSelectionCases
public import HexRCF.SourceSelectionNegative
public import HexRCF.ProofEvidence

public section
namespace Hex.RCF.SourceSelectionConformance
open Hex Hex.RealClosure Hex.RealFormula Hex.RCF.RealCoefficients
open scoped Hex

def inputs : SourceSelection 4 :=
  .coordinate (.inherited (.coordinate (.root .nil SourceSelectionCases.root)
    0 #p[0,-1])) 0 #p[-1,0,1]

noncomputable def source : Fin 4 → ℝ := ![Real.sqrt 2, -Real.sqrt 2, 2, 1]

/-- Authentication compares each source term to the generated interpretation;
no client proof unfolds the selector's conjunctions or formula renamings. -/
theorem authenticated_inherited (inherited : ℝ) :
    inputs.formula.toProp ![Real.sqrt 2, -Real.sqrt 2, inherited, 1] := by
  apply (inputs.formula_iff _).mpr
  funext i
  fin_cases i <;>
    norm_num [inputs, SourceSelection.real, RealFormula.append, Function.comp_def,
      SourceSelectionCases.selected, realPoly, HexPolyTheory.Interpret.interpret_map,
      DensePoly.Interpret.map_ofCoeffs, HexPolyTheory.toPolynomial_ofCoeffs,
      Finset.sum_range_succ, ratCast, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

theorem authenticated : inputs.formula.toProp source := authenticated_inherited 2

/-- The selector deliberately leaves inherited values to their actual origin.
This different tuple also satisfies it, so inherited evidence is necessary. -/
theorem inherited_free : inputs.formula.toProp ![Real.sqrt 2, -Real.sqrt 2, 3, 1] :=
  authenticated_inherited 3

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

/-- Swapping the two computed coordinates is also rejected. -/
theorem swapped : ¬ inputs.formula.toProp ![Real.sqrt 2,1,2,-Real.sqrt 2] := by
  intro meaning
  have same := congrFun (unique _ rfl meaning) 1
  change (1 : ℝ) = -Real.sqrt 2 at same
  nlinarith [Real.sqrt_nonneg (2 : ℝ)]

/-- A computed coordinate may be the next generator. The final relation uses
non-integral rationals and its positive denominator-clearing multiplier is 15. -/
def chain : SourceSelection 3 :=
  .coordinate (.coordinate (.inherited .nil) 0 (DensePoly.ofCoeffs #[1,1]))
    1 (DensePoly.ofCoeffs #[1/3,2/5])

theorem chain_source : chain.formula.toProp ![2,3,23/15] := by
  apply (chain.formula_iff _).mpr
  funext i
  fin_cases i <;>
    norm_num [chain, SourceSelection.real, RealFormula.append, Function.comp_def,
      realPoly, HexPolyTheory.Interpret.interpret_map, DensePoly.Interpret.map_ofCoeffs,
      HexPolyTheory.toPolynomial_ofCoeffs, Finset.sum_range_succ, ratCast]

theorem wrong_chain : ¬ chain.formula.toProp ![2,3,22/15] := by
  intro meaning
  have last := congrFun ((chain.formula_iff _).mp meaning) 2
  norm_num [chain, SourceSelection.real, RealFormula.append, realPoly,
    HexPolyTheory.Interpret.interpret_map, DensePoly.Interpret.map_ofCoeffs,
    HexPolyTheory.toPolynomial_ofCoeffs, Finset.sum_range_succ, ratCast] at last

theorem two_roots {firstVersion secondVersion : Nat}
    (first : Root firstVersion) (second : Root secondVersion) :
    (SourceSelection.root (.root .nil first) second).formula.toProp ![first.real,second.real] := by
  apply (SourceSelection.formula_iff _ _).mpr
  funext i
  fin_cases i <;> simp [SourceSelection.real, RealFormula.append]

theorem swapped_roots {firstVersion secondVersion : Nat}
    (first : Root firstVersion) (second : Root secondVersion) (different : first.real ≠ second.real) :
    ¬ (SourceSelection.root (.root .nil first) second).formula.toProp ![second.real,first.real] := by
  intro meaning
  have same := congrFun ((SourceSelection.formula_iff _ _).mp meaning) 0
  apply different
  simpa [SourceSelection.real, RealFormula.append] using same.symm

theorem concrete_roots :
    (SourceSelection.root (.root .nil SourceSelectionCases.root) SourceSelectionNegative.root).formula.toProp
      ![Real.sqrt 2,-Real.sqrt 2] := by
  simpa only [SourceSelectionCases.selected, SourceSelectionNegative.selected] using
    two_roots SourceSelectionCases.root SourceSelectionNegative.root

theorem concrete_swap :
    ¬ (SourceSelection.root (.root .nil SourceSelectionCases.root) SourceSelectionNegative.root).formula.toProp
      ![-Real.sqrt 2,Real.sqrt 2] := by
  have different : SourceSelectionCases.root.real ≠ SourceSelectionNegative.root.real := by
    rw [SourceSelectionCases.selected, SourceSelectionNegative.selected]
    have positive := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
    linarith
  simpa only [SourceSelectionCases.selected, SourceSelectionNegative.selected] using
    swapped_roots SourceSelectionCases.root SourceSelectionNegative.root different

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
  obtain ⟨read, domain, closed, negative, identified, present, sizes, meaning, guarded, base⟩ :=
    inputs.exists_real context following values source authenticated (by
      intro i inherited
      have same := (inherited_exact i).mp inherited
      subst i
      exact fixed) sample matrix guards nonzero truth
  exact ⟨read sample, meaning⟩

run_meta do
  for name in #[``authenticated,``authenticated_inherited,``inherited_free,``unique,
      ``wrong_conjugate,``swapped,``chain_source,``two_roots,``swapped_roots,``realize,
      ``SourceSelection.unique,``SourceSelection.exists_real] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
      Lean.throwError m!"source selection has unexpected axioms: {name}: {axioms}"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies #[``realize]
  for law in #[``SourceSelection.exists_real,``SourceSelection.unique,``NativeSources.true_real] do
    unless dependencies.contains law do
      Lean.throwError m!"source selection omitted its shared or finite-realization law: {law}"

end Hex.RCF.SourceSelectionConformance
