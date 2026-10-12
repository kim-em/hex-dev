/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RootReplayConformance
import HexRCF.ProofEvidence

namespace Hex.RCF.RealCoefficients.RootReplayOrdinaryConformance
open Hex Hex.RealClosure Hex.SignDet Hex.RCF.SelectedRootTests
open RootReplayConformance HexPolyMathlib.Interpret HexRealRootsMathlib

private theorem interpreted : interpret Data.rational.value Data.rational.zero_iff polynomial =
    (Polynomial.X ^ 2 - 2 : Polynomial ℝ) := by
  have same := Data.definingPoly
  rw [Data.lowerData.1] at same
  exact same

/-- A fresh ordinary-kernel proof consumes an emitted descriptor, its actual
checked domain and its owner root interpretation, without invoking production. -/
theorem source : ∃ x : ℝ, x ^ 2 = 2 ∧ 1 < x ∧ x < 2 := by
  have word : [1,1] ∈ positiveResult.roots.map (fun d => d.raw.signs) := by
    rw [positive_words]
    simp
  obtain ⟨d, member, _⟩ := List.mem_map.mp word
  let x := d.root Data.rational.value Data.rational.zero_iff Data.rational.one Data.rational.add
    Data.rational.sub Data.rational.mul Data.rational.nat Data.rational.sign
  have root := positiveResult.root_spec Data.rational d member
  have valid := positiveResult.domain Data.rational
  have facts := (Tarski.mem_rootsIn_iff _ valid.1 _ _ x).mp root
  rw [interpreted] at facts
  refine ⟨x, ?_⟩
  simpa [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero,
    Endpoint.map, Data.rationalOne, Data.rationalTwo] using facts

#print axioms source
open Lean Meta in
run_meta do
  for law in #[``RootReplay.Result.root_spec, ``RootReplay.Result.domain] do
    unless ← Hex.RCF.ProofEvidence.contains ``source (fun e => e.isConstOf law) do
      throwError "fresh root source omitted replay interpretation {law}"
  for producer in #[``Descriptor.buildRoots, ``Hex.SignDet.buildPrepared,
      ``Hex.SignDet.buildTree, ``Hex.SignDet.buildTreeFrom] do
    if ← Hex.RCF.ProofEvidence.contains ``source (fun e => e.isConstOf producer) then
      throwError "fresh root source retained a producer {producer}"
  for axiomName in (← collectAxioms ``source) do
    unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
      throwError "fresh root source has unapproved axiom {axiomName}"

end Hex.RCF.RealCoefficients.RootReplayOrdinaryConformance
