/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RootReplayConformance
import HexRCF.ProofEvidence
import HexRCF.Tactic

namespace Hex.RCF.RealCoefficients.RootReplayOrdinaryConformance
open Hex Hex.RealClosure Hex.SignDet Hex.RCF.SelectedRootTests
open RootReplayConformance HexPolyMathlib.Interpret HexRealRootsMathlib
open scoped Hex

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

/-- The negative full derivative word selects the negative conjugate in the
same accepted whole-line table, independently of the separate (1,2) fixture. -/
theorem negative : ∃ x : ℝ, x ^ 2 = 2 ∧ x < 0 := by
  have word : [-1,1] ∈ wholeResult.roots.map (fun d => d.raw.signs) := by
    rw [whole_words]
    simp
  obtain ⟨d, member, signWord⟩ := List.mem_map.mp word
  let x := d.root Data.rational.value Data.rational.zero_iff Data.rational.one Data.rational.add
    Data.rational.sub Data.rational.mul Data.rational.nat Data.rational.sign
  have root := wholeResult.root_spec Data.rational d member
  have valid := wholeResult.domain Data.rational
  have facts := (Tarski.mem_rootsIn_iff _ valid.1 _ _ x).mp root
  rw [interpreted] at facts
  have square : x ^ 2 = 2 := by
    simpa [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero] using facts.1
  obtain ⟨word, raw⟩ := wholeResult.fields d member
  have head : d.raw.head = polynomial := by rw [raw]; rfl
  have indices : d.raw.indices = [1,2] := by
    rw [raw]
    change ((RootReplay.subject polynomial .negInf .posInf).full []).indices = [1,2]
    decide +kernel
  have derivatives := d.root_derivatives Data.rational.value Data.rational.zero_iff
    Data.rational.one Data.rational.add Data.rational.sub Data.rational.mul Data.rational.nat
    Data.rational.sign
  rw [head, indices, interpreted, signWord] at derivatives
  have first := congrArg (fun words : List Int => words.head!) derivatives
  have sign : (SignType.sign (2*x) : Int) = -1 := by
    simpa [Function.iterate_succ_apply, Polynomial.derivative_sub,
      Polynomial.derivative_X_pow, x, show (1 : ℝ) + 1 = 2 by norm_num] using first.symm
  have negative : SignType.sign (2*x) = -1 := by
    generalize h : SignType.sign (2*x) = s at sign ⊢
    cases s with
    | neg => rfl
    | zero => change (0 : Int) = -1 at sign; norm_num at sign
    | pos => change (1 : Int) = -1 at sign; norm_num at sign
  exact ⟨x, square, by have := sign_eq_neg_one_iff.mp negative; linarith⟩

/-- The accepted whole-line table contains every real root, including roots
not chosen by either of the earlier existential witness proofs. -/
theorem all_roots (x : ℝ) : x ∈ wholeResult.values Data.rational ↔ x ^ 2 = 2 := by
  have valid := wholeResult.domain Data.rational
  calc
    x ∈ wholeResult.values Data.rational ↔
        x ∈ Tarski.rootsIn (interpret Data.rational.value Data.rational.zero_iff polynomial)
          .negInf .posInf := ((wholeResult.coverage Data.rational).1 x).symm
    _ ↔ x ^ 2 = 2 := by
      rw [Tarski.mem_rootsIn_iff _ valid.1, interpreted]
      simp [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]

/-- The full empty table excludes every real root of the nonzero constant. -/
theorem constant_coverage (x : ℝ) :
    x ∉ Tarski.rootsIn (interpret Data.rational.value Data.rational.zero_iff
      (1 : Data.base.Poly)) .negInf .posInf := by
  have absent : constantResult.roots = [] := List.length_eq_zero_iff.mp constant_empty
  intro present
  have member := ((constantResult.coverage Data.rational).1 x).mp present
  simp only [RootReplay.Result.values, absent, List.map_nil, List.not_mem_nil] at member

/-- An empty nonconstant table proves absence, rather than just emitting no roots. -/
theorem empty_coverage (x : ℝ) :
    x ∉ Tarski.rootsIn (interpret Data.rational.value Data.rational.zero_iff
      (#p[1,0,1] : Data.base.Poly)) .negInf .posInf := by
  have absent : emptyResult.roots = [] := List.length_eq_zero_iff.mp empty_empty
  intro present
  have member := ((emptyResult.coverage Data.rational).1 x).mp present
  simp only [RootReplay.Result.values, absent, List.map_nil, List.not_mem_nil] at member

/-- Distinct full words denote distinct roots in this accepted table. -/
theorem unique : (wholeResult.values Data.rational).Nodup :=
  (wholeResult.coverage Data.rational).2

/-- The returned order is mathematical strict order. -/
theorem ordered : (wholeResult.values Data.rational).Pairwise (· < ·) :=
  wholeResult.ordered Data.rational

/-- info: 'Hex.RCF.RealCoefficients.RootReplayOrdinaryConformance.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source
/-- info: 'Hex.RCF.RealCoefficients.RootReplayOrdinaryConformance.negative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms negative
open Lean Meta in
run_meta do
  for name in #[``source, ``negative] do
    for law in #[``RootReplay.Result.root_spec, ``RootReplay.Result.domain] do
      unless ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf law) do
        throwError "fresh root source omitted replay interpretation {law}"
    for producer in #[``Descriptor.buildRoots, ``Hex.SignDet.buildPrepared,
        ``Hex.SignDet.buildTree, ``Hex.SignDet.buildTreeFrom] do
      if ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf producer) then
        throwError "fresh root source retained a producer {producer}"
    for axiomName in (← collectAxioms name) do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
        throwError "fresh root source has unapproved axiom {axiomName}"
  for law in #[``RootReplay.Result.fields, ``Descriptor.root_derivatives] do
    unless ← Hex.RCF.ProofEvidence.contains ``negative (fun e => e.isConstOf law) do
      throwError "negative conjugate omitted its checked derivative identity {law}"

open Lean Meta in
run_meta do
  for (name, law, owner) in #[
      (``all_roots, ``RootReplay.Result.coverage, ``Descriptor.rootsFrom_coverage),
      (``constant_coverage, ``RootReplay.Result.coverage, ``Descriptor.rootsFrom_coverage),
      (``empty_coverage, ``RootReplay.Result.coverage, ``Descriptor.rootsFrom_coverage),
      (``unique, ``RootReplay.Result.coverage, ``Descriptor.rootsFrom_coverage),
      (``ordered, ``RootReplay.Result.ordered, ``Descriptor.rootsFrom_ordered)] do
    let .thmInfo info ← getConstInfo name | throwError "expected actual frozen coverage proof"
    let _ ← Hex.RCF.checkProof name info.type info.value
    unless ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf law) do
      throwError "supplied coverage omitted adapter law {law}"
    let wrapper ← getConstInfo law
    let some body := wrapper.value? (allowOpaque := true) | throwError "missing adapter proof body"
    let _ ← Hex.RCF.checkProof law wrapper.type body
    unless body.getUsedConstants.contains owner do
      throwError "adapter wrapper omitted actual owner law {owner}"
    for producer in #[``Descriptor.buildRoots, ``Hex.SignDet.buildPrepared,
        ``Hex.SignDet.buildTree, ``Hex.SignDet.buildTreeFrom] do
      if ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf producer) then
        throwError "supplied coverage retained native production {producer}"
    let axioms ← collectAxioms name
    unless axioms.size == 3 && axioms.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "unexpected frozen-coverage theorem axioms"

end Hex.RCF.RealCoefficients.RootReplayOrdinaryConformance
