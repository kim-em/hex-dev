/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.NestedTransport.Source
import HexRCF.NestedTransport.Controls
import HexRCF.RealCoefficients
import HexRCF.ProofEvidence
-- These imports let forbidden proof names resolve and fail on renames.
import HexRCF.SelectedRoot.Proofs
import HexRCF.SelectedRoot.CatalogSource
import HexRCF.SectionReplayConformance
import HexRCF.NestedRootProduceConformance
import Lean.Elab.Command
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests
namespace Hex.RCF.RealCoefficients.NestedTransportTests.Ordinary
open Data Hex.RCF.RealCoefficients.NestedTransportTests.Source
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
-- Re-derive the identity locally: the positive owner-law scan treats imported
-- Model.point_eq as a leaf.
theorem point_eq : Hex.RCF.RealCoefficients.NestedTransportTests.Model.point = Upper.root.root original.value original.zero_iff original.one
    original.add original.sub original.mul original.nat original.sign :=
  Hex.RCF.RealCoefficients.NestedTransportTests.Model.interpretation.root Upper.root
    Hex.RCF.RealCoefficients.NestedTransportTests.Model.checked.converted Hex.RCF.RealCoefficients.NestedTransportTests.Model.checked.binding
open HexPolyMathlib.Interpret HexRealRootsMathlib in
theorem point : Hex.RCF.RealCoefficients.NestedTransportTests.Model.point ^ 2 = Real.sqrt 2 ∧
    1 < Hex.RCF.RealCoefficients.NestedTransportTests.Model.point ∧ Hex.RCF.RealCoefficients.NestedTransportTests.Model.point < 2 := by
  rw [point_eq]
  let x := Upper.root.root original.value original.zero_iff original.one original.add original.sub
    original.mul original.nat original.sign
  have member := (Upper.root.root_spec original.value original.zero_iff original.one original.add
    original.sub original.mul original.nat original.sign).1
  have valid := Upper.root.head_ne_zero original.value original.zero_iff
  have data := (Tarski.mem_rootsIn_iff _ valid _ _ x).mp member
  rw [fields.1, interpreted] at data
  have lo : original.value Hex.RCF.RealCoefficients.NestedTransportTests.Source.lower = 1 := by
    unfold Hex.RCF.RealCoefficients.NestedTransportTests.Source.lower
    erw [Algebraic.Element.cachedOne_eq, original.one]
  have hi : original.value Hex.RCF.RealCoefficients.NestedTransportTests.Source.upper = 2 := by
    unfold Hex.RCF.RealCoefficients.NestedTransportTests.Source.upper
    have same := congrArg (fun op : NatCast parent.Value => original.value (@NatCast.natCast parent.Value op 2))
      (Algebraic.Element.cachedNatCast_eq reduction reduction_eq Hex.RCF.RealCoefficients.NestedTransportTests.Predecessor.facts)
    exact same.trans (original.nat 2)
  refine ⟨?_, ?_⟩
  · simpa only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, sub_eq_zero] using data.1
  · rw [fields.2.1, fields.2.2] at data
    have bounds := data.2
    change original.value Hex.RCF.RealCoefficients.NestedTransportTests.Source.lower < x ∧ x < original.value Hex.RCF.RealCoefficients.NestedTransportTests.Source.upper at bounds
    simpa only [lo, hi] using bounds

theorem source : ∃ x : ℝ, x ^ 2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 :=
  ⟨Hex.RCF.RealCoefficients.NestedTransportTests.Model.point, point⟩
/-- info: 'Hex.RCF.RealCoefficients.NestedTransportTests.Ordinary.source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms source
open Lean in
run_meta do
  for name in #[``source, ``point_eq] do
    let .thmInfo info ← getConstInfo name | throwError "expected local theorem body"
    let _ ← Hex.RCF.checkProof name info.type info.value
    let axioms ← collectAxioms name
    unless axioms.size == 3 && axioms.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "unapproved frozen suffix axiom"
  for law in #[``Descriptor.root_spec, ``Conversion.Model.root] do
    unless ← Hex.RCF.ProofEvidence.contains ``source (fun e => e.isConstOf law) do
      throwError "fresh source omitted actual root law"
  let forbidden := #[``Hex.RCF.RealCoefficients.NestedRootProduceConformance.source,
    ``Hex.RCF.SelectedRootTests.CatalogSource.source,
    ``Hex.RCF.SelectedRootTests.Source.source,
    ``Hex.RCF.SelectedRootTests.Proofs.rowAccepted,
    ``Hex.RCF.RealCoefficients.SectionReplayConformance.source,
    ``Hex.RCF.SelectedRootTests.Row.rowResult,
    ``Hex.RCF.RealCoefficients.SelectedFormula.row_sound,
    ``Hex.RCF.RealCoefficients.SelectedFormula.row_spec,
    ``Hex.RCF.RealCoefficients.SectionReplay.check_sound,
    ``Hex.RCF.RealCoefficients.SectionReplayConformance.checked,
    ``Hex.RCF.RealCoefficients.SectionReplayConformance.accepted]
  let environment ← getEnv
  let moduleNames := environment.header.moduleNames
  let upstream := #[`Init, `Lean, `Std, `Batteries, `Mathlib, `Aesop, `Qq, `TauCeti]
  let mut pending := [``source]
  let mut seen : NameHashSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    if forbidden.contains name then
      throwError "fresh source transitively used an earlier row/source proof: {name}"
    -- Upstream packages are built before this project and cannot reference
    -- its declarations. Follow all project library and conformance types/bodies.
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := moduleNames[index]!
      if upstream.any (fun boundary => boundary.isPrefixOf moduleName) then continue
    let info ← getConstInfo name
    pending := info.type.getUsedConstants.toList ++ pending
    if let some body := info.value? (allowOpaque := true) then
      pending := body.getUsedConstants.toList ++ pending
open Lean in
run_meta do
  let environment ← getEnv
  let moduleNames := environment.header.moduleNames
  for (name, info) in environment.constants do
    let belongs := if let some index := environment.getModuleIdxFor? name then
      (`HexRCF.NestedTransport).isPrefixOf moduleNames[index]!
    else
      (`Hex.RCF.RealCoefficients.NestedTransportTests).isPrefixOf name ||
        name.toString.startsWith "_private.HexRCF.NestedTransport."
    if belongs then
      if let .thmInfo theoremInfo := info then
        if theoremInfo.value.hasSorry || theoremInfo.value.hasMVar ||
            theoremInfo.type.hasSorry || theoremInfo.type.hasMVar then
          throwError "incomplete theorem {name}"
        for axiomName in ← collectAxioms name do
          unless #[``propext, ``Classical.choice, ``Quot.sound].contains axiomName do
            throwError "unapproved axiom {axiomName} through {name}"
end Hex.RCF.RealCoefficients.NestedTransportTests.Ordinary
