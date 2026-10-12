/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.NativeSelection
public import HexRCF.RealCoefficients.NativeSources
public import HexRCF.Tactic
public import HexRCF.ProofEvidence
public section
namespace Hex.RCF.RealCoefficients.NativeSelectionOrdinaryConformance
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.RealFormula Hex.RCF.RealCoefficients

theorem witness {registry : BaseContext.Registry} (context : Context registry)
    (following : context.origin.base.Realization) {version : Nat} (root : Root version)
    (coordinate sample : context.Value) (formula : RealFormula.QF 2) (guards : List context.Value)
    (nonzero : ∀ a ∈ guards, context.sign a ≠ 0)
    (truth : Samples.Row.eval (.and (NativeSelection.selection 0 root.raw).lift formula)
      (NativeSpecialize.row context (fun _ => coordinate) sample
        (.and (NativeSelection.selection 0 root.raw).lift formula)) = some true) :
    ∃ x : ℝ, formula.toProp (RealFormula.append (fun _ => root.real) x) := by
  obtain ⟨read, domain, closed, negative, fixed, present, sizes, meaning, guarded, inherited⟩ :=
    NativeSources.true_real context following (fun _ => coordinate) (fun _ => root.real)
      (NativeSelection.selection 0 root.raw)
      (fun coefficients _ selected => NativeSelection.unique root coefficients selected)
      sample formula guards nonzero truth
  exact ⟨read sample, meaning⟩

/-- info: 'Hex.RCF.RealCoefficients.NativeSelectionOrdinaryConformance.witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms witness

run_meta do
  let name := ``witness
  let _ ← Hex.RCF.checkProof name (← Lean.Meta.inferType (Lean.mkConst name)) (Lean.mkConst name)
  for law in #[``NativeSources.true_real, ``NativeSelection.unique] do
    unless ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf law) do
      Lean.throwError "fresh root selection omitted its source or finite reader law"
  let axioms ← Lean.collectAxioms name
  unless axioms.size == 3 && axioms.all
      (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
    Lean.throwError "fresh root selection has an unexpected complete axiom inventory"
end Hex.RCF.RealCoefficients.NativeSelectionOrdinaryConformance
