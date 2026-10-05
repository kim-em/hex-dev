/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.RealizationData
import HexRCF.ProofEvidence
import HexRCF.Tactic
import HexSignDet.Produce
import HexSignDet.TableProducer
import HexSignDet.DagExpand

/-! Frozen one-infinitesimal replay for the complete shared `(1, 2]` guard
conjunction. The ordinary witness follows from the owner realization law;
no producer is called to supply the literal count or moment certificates. -/

open Hex Hex.RealFormula Hex.SignDet Hex.RCF.RealCoefficients
open Realization
open scoped Hex
attribute [local instance 2500] Field.toGrindField
namespace Hex.RCF.RealizationTests
set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private theorem prepared : RepresentationSpecialize.prepare values formula =
    [DensePoly.ofList [-1, 1], DensePoly.ofList [-2, 1]] := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private theorem lifted : Realization.lift (DensePoly.ofList [-1, 1] : DensePoly Rat) =
    first := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
private theorem lifted_second : Realization.lift (DensePoly.ofList [-2, 1] : DensePoly Rat) =
    second := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem checked : replay.check sign 7 p (.finite 1) (.finite 2)
    (queries values formula) = true := by
  unfold queries
  rw [prepared]
  simp only [List.map_cons, List.map_nil, lifted, lifted_second]
  decide +kernel

theorem source : ∃ x : ℝ, formula.toProp
    (append (fun i => (Rat.castHom ℝ) (values i)) x) :=
  exists_real (Rat.castHom ℝ) Rat.cast_strictMono 7 values formula p
    (.finite 1) (.finite 2) replay checked [1, -1]
    (by simp only [replay, Replay.table, node]; decide +kernel) (by decide +kernel)

theorem bounded : ∃ x : ℝ, 1 < x ∧ x ≤ 2 := by
  obtain ⟨x, hx⟩ := source
  refine ⟨x, ?_⟩
  unfold formula at hx
  have two : HexMvPolyMathlib.toMvPolynomial (2 : Poly 2) = 2 := by
    change HexMvPolyMathlib.toMvPolynomial (MvPoly.C (2 : Int)) = 2
    simp
  simp only [QF.toProp, RealFormula.Atom.toProp, RealFormula.Cmp.toProp, RealFormula.Poly.eval,
    ← HexMvPolyMathlib.eval₂_toMvPolynomial] at hx
  simpa [append, values, two] using hx

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem reject_context : replay.check sign 8 p (.finite 1) (.finite 2)
    (queries values formula) = false := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem reject_coefficients : replay.check sign 7 p (.finite 1) (.finite 2)
    (queries (fun _ : Fin 1 => (2 : Rat)) formula) = false := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem reject_leaf : (Replay.leaf node).check sign 7 p (.finite 1) (.finite 2)
    (queries values formula) = false := by decide +kernel

theorem reject_condition : (replay.table checked).count [1, 1] = 0 ∧
    Samples.Row.eval formula [1, 1] = some false := by
  simp only [replay, Replay.table, node]
  decide +kernel

/-- Negation retains the accepted queries and count-one row, but its Boolean
truth is false: the truth premise is independent of replay acceptance. -/
theorem checked_not : replay.check sign 7 p (.finite 1) (.finite 2)
    (queries values formula.not) = true := by
  simpa only [queries, RepresentationSpecialize.prepare, QF.polys_not] using checked

theorem reject_truth : (replay.table checked_not).count [1, -1] = 1 ∧
    Samples.Row.eval formula.not [1, -1] = some false := by
  simp only [replay, Replay.table, node]
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem reject_order : replay.check sign 7 p (.finite 1) (.finite 2)
    (queries values formula).reverse = false := by decide +kernel

theorem reject_row : Samples.Row.eval formula [1] = none := by decide +kernel

end Hex.RCF.RealizationTests

/-- info: 'Hex.RCF.RealizationTests.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RCF.RealizationTests.source
/-- info: 'Hex.RCF.RealizationTests.bounded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RCF.RealizationTests.bounded
/-- info: 'Hex.RCF.RealCoefficients.Realization.exists_real' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RCF.RealCoefficients.Realization.exists_real

/-- Follow the complete literal-data definition closure. Within query/sign/root
namespaces permit only types, constructors, projections, proofs and frozen count indexing;
certificate producers and unlisted computational helpers are rejected. -/
private meta partial def auditData (moduleIndex : Lean.ModuleIdx)
    (seen : Lean.NameHashSet) (name : Lean.Name) : Lean.MetaM Lean.NameHashSet := do
  if seen.contains name then return seen
  let mut seen := seen.insert name
  let info ← Lean.getConstInfo name
  let some body := info.value? (allowOpaque := true) |
    throwError "missing literal fixture body {name}"
  for called in body.getUsedConstants do
    let visible := (Lean.privateToUserName? called).getD called
    if (`Hex.Sturm).isPrefixOf visible || (`Hex.SignDet).isPrefixOf visible ||
        (`Hex.RealClosure).isPrefixOf visible then
      let calledInfo ← Lean.getConstInfo called
      let harmless := called == ``Hex.SignDet.System.positive ||
        ((← Lean.getEnv).getProjectionFnInfo? called).isSome ||
        match calledInfo with
        | .ctorInfo _ | .inductInfo _ | .recInfo _ | .thmInfo _ => true
        | _ => false
      unless harmless do
        throwError "literal fixture {name} contains query/sign/root computation {called}"
    if (← Lean.getEnv).getModuleIdxFor? called == some moduleIndex then
      seen ← auditData moduleIndex seen called
  return seen

run_meta do
  for name in #[``Hex.RCF.RealizationTests.checked, ``Hex.RCF.RealizationTests.source,
      ``Hex.RCF.RealizationTests.bounded, ``Hex.RCF.RealizationTests.reject_context,
      ``Hex.RCF.RealizationTests.reject_coefficients, ``Hex.RCF.RealizationTests.reject_leaf,
      ``Hex.RCF.RealizationTests.reject_condition, ``Hex.RCF.RealizationTests.reject_row,
      ``Hex.RCF.RealizationTests.checked_not, ``Hex.RCF.RealizationTests.reject_truth,
      ``Hex.RCF.RealizationTests.reject_order,
      ``Hex.RCF.RealCoefficients.Realization.lift_eval,
      ``Hex.RCF.RealCoefficients.Realization.signs,
      ``Hex.RCF.RealCoefficients.Realization.exists_real] do
    Hex.RCF.checkAxioms name (Lean.mkConst name)
  let producers := #[``Hex.Sturm.query, ``Hex.Sturm.queryPrepared,
    ``Hex.RealClosure.Tower.Sample.family, ``Hex.SignDet.buildNode,
    ``Hex.SignDet.buildTreeFrom, ``Hex.SignDet.buildTree, ``Hex.SignDet.buildPrepared,
    ``Hex.SignDet.buildTablePrepared, ``Hex.SignDet.Dag.Expansion.run]
  let some dataModule := (← Lean.getEnv).getModuleIdxFor? ``Hex.RCF.RealizationTests.replay |
    throwError "missing imported literal-data module"
  let mut seen : Lean.NameHashSet := {}
  for name in #[``Hex.RCF.RealizationTests.replay, ``Hex.RCF.RealizationTests.values,
      ``Hex.RCF.RealizationTests.formula, ``Hex.RCF.RealizationTests.sign] do
    seen ← auditData dataModule seen name
  for (name, markers) in #[(``Hex.RCF.RealCoefficients.Realization.exists_real,
      #[``Hex.RealClosure.Specialize.realizeBelow,
        ``Hex.RCF.RealCoefficients.Samples.Row.eval_true]),
      (``Hex.RealClosure.Specialize.realizeBelow,
        #[``Hex.RealClosure.Specialize.realizeReplay])] do
    let info ← Lean.getConstInfo name
    let some body := info.value? (allowOpaque := true) |
      throwError "missing ordinary theorem body {name}"
    for marker in markers do
      unless (body.find? (fun e => e.isConstOf marker)).isSome do
        throwError "ordinary theorem {name} omitted {marker}"
  for name in #[``Hex.RCF.RealizationTests.source, ``Hex.RCF.RealizationTests.bounded] do
    for marker in #[``Hex.RCF.RealCoefficients.Realization.exists_real,
        ``Hex.RCF.RealizationTests.checked] do
      unless ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf marker) do
        throwError "ordinary source proof {name} omitted checked realization boundary {marker}"
    for forbidden in producers do
      if ← Hex.RCF.ProofEvidence.contains name (fun e => e.isConstOf forbidden) then
        throwError "ordinary source proof contains native production"
