/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Guards.Controls
import HexRCF.FiniteMatrix.Guards.Domains
import HexRCF.FiniteMatrix.Guards.Refusals
import HexRCF.FiniteMatrix.Ordinary
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Ordinary
open Lean Meta Hex.RealClosure.Algebraic.KernelReplay
run_meta do
  let environment ← getEnv
  let moduleNames := environment.header.moduleNames
  let forbidden := #[``Hex.RCF.RealCoefficients.FiniteMatrixTests.Quote.original,
    ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Quote.guarded,
    ``FiniteJoint.joint, ``FiniteJoint.exists_joint, ``FiniteJoint.nextData,
    ``Hex.RCF.RealCoefficients.NestedTransportTests.Ordinary.source,
    ``Hex.RCF.RealCoefficients.NestedRootProduceConformance.source,
    ``Hex.RCF.SelectedRootTests.CatalogSource.source,
    ``Hex.RCF.SelectedRootTests.Source.source,
    ``Hex.RCF.SelectedRootTests.Proofs.rowAccepted,
    ``Hex.RCF.RealCoefficients.SectionReplayConformance.source,
    ``Hex.RCF.SelectedRootTests.Row.rowResult,
    ``Hex.RCF.RealCoefficients.SelectedFormula.row_sound,
    ``Hex.RCF.RealCoefficients.SelectedFormula.row_spec,
    ``Hex.RCF.RealCoefficients.SectionReplay.check_sound]
  let required := #[``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Data.accepted, ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Data.replay,
    ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Binding.bind, ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Binding.valuation_eq,
    ``Hex.RCF.RealCoefficients.FiniteSigns.check_sound,
    ``Hex.RealClosure.Transport.Finite.ReplayData.of_closed,
    ``Hex.RealClosure.Transport.Inventory.replay_data,
    ``Hex.RealClosure.Algebraic.Element.denote_mul,
    ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Semantics.read_eq,
    ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Semantics.root,
    ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Semantics.alpha_sqrt,
    ``Hex.SignDet.Descriptor.root_unique]
  let .thmInfo info ← getConstInfo ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quote.original | throwError "expected quoted original"
  let _ ← Hex.RCF.checkProof ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quote.original info.type info.value
  let axioms ← collectAxioms ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quote.original
  unless axioms.size == 3 && axioms.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
    throwError "unexpected complete source axiom inventory"
  let mut pending := [``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quote.original]
  let mut seen : NameHashSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    if forbidden.contains name then throwError "source reused a prior existential: {name}"
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := moduleNames[index]!
      if #[`Init, `Lean, `Std, `Batteries, `Mathlib, `Aesop, `Qq, `TauCeti].any
          (fun boundary => boundary.isPrefixOf moduleName) then continue
    let declaration ← getConstInfo name
    pending := declaration.type.getUsedConstants.toList ++ pending
    if let some body := declaration.value? (allowOpaque := true) then
      pending := body.getUsedConstants.toList ++ pending
  for name in required do unless seen.contains name do throwError "source omitted actual owner evidence: {name}"
  let .thmInfo domains ← getConstInfo ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Domains.original | throwError "expected original domains"
  let _ ← Hex.RCF.checkProof ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Domains.original domains.type domains.value
  let axioms ← collectAxioms ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Domains.original
  unless axioms.size == 3 && axioms.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
    throwError "unexpected original-domain axiom inventory"
  for (name, declaration) in environment.constants do
    let belongs := if let some index := environment.getModuleIdxFor? name then
      (`HexRCF.FiniteMatrix.Guards).isPrefixOf moduleNames[index]!
    else (`Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards).isPrefixOf name
    if belongs && declaration.isTheorem then
      let axioms ← collectAxioms name
      unless axioms.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
        throwError "unexpected guard theorem axiom: {name}"
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Ordinary
