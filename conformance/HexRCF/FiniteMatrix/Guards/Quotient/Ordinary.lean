/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Guards.Quotient.Controls
import HexRCF.FiniteMatrix.Guards.Ordinary
open Lean Meta Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Ordinary
run_meta do
  let environment ← getEnv
  let moduleNames := environment.header.moduleNames
  let forbidden := #[``Hex.RCF.RealCoefficients.FiniteMatrixTests.Quote.original,
    ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Quote.guarded,
    ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quote.original,
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
    ``Hex.RCF.RealCoefficients.SectionReplay.check_sound,
    ``Packing.Inverse.build?, ``Packing.Inverse.makeCandidate?, ``Packing.Inverse.toEquation]
  let required := #[``Quote.accepted, ``Binding.bind, ``Binding.valuation_eq,
    ``Binding.inverse, ``Binding.argument_eq, ``Reader.read_argument,
    ``Records.inverse.read_eq, ``Source.computed,
    ``Hex.RealClosure.Algebraic.Packing.Inverse.Equation.denote_inv,
    ``Hex.RCF.RealCoefficients.FiniteSigns.check_sound,
    ``Hex.RealClosure.Transport.Finite.ReplayData.of_closed,
    ``Hex.RealClosure.Transport.Inventory.replay_data,
    ``Hex.RealClosure.Algebraic.Element.denote_mul,
    ``Hex.RCF.RealCoefficients.FiniteMatrixTests.Semantics.read_eq,
    ``Hex.SignDet.Descriptor.root_unique]
  for name in #[``Quote.original, ``Binding.inverse] do
    let .thmInfo info ← getConstInfo name | throwError "expected actual quotient proof body"
    let _ ← Hex.RCF.checkProof name info.type info.value
    let axioms ← collectAxioms name
    unless axioms.size == 3 && axioms.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "unexpected complete quotient-source axiom inventory"
  let mut pending := [``Quote.original]
  let mut seen : NameHashSet := {}
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    if forbidden.contains name then throwError "quotient source used a forbidden witness or inverse producer: {name}"
    if let some index := environment.getModuleIdxFor? name then
      let moduleName := moduleNames[index]!
      if #[`Init, `Lean, `Std, `Batteries, `Mathlib, `Aesop, `Qq, `TauCeti].any
          (fun boundary => boundary.isPrefixOf moduleName) then continue
    let declaration ← getConstInfo name
    pending := declaration.type.getUsedConstants.toList ++ pending
    if let some body := declaration.value? (allowOpaque := true) then
      pending := body.getUsedConstants.toList ++ pending
  for name in required do unless seen.contains name do throwError "quotient source omitted actual evidence: {name}"
  for (name, declaration) in environment.constants do
    let belongs := if let some index := environment.getModuleIdxFor? name then
      (`HexRCF.FiniteMatrix.Guards.Quotient).isPrefixOf moduleNames[index]!
    else (`Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient).isPrefixOf name
    if belongs && declaration.isTheorem then
      let axioms ← collectAxioms name
      unless axioms.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
        throwError "unexpected quotient theorem axiom: {name}"
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Guards.Quotient.Ordinary
