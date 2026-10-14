/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Quote
import HexRCF.FiniteMatrix.Controls
import HexRCF.FiniteMatrix.Refusals
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Ordinary
open Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open Lean Meta
/- Check actual source-proof bodies and every project dependency, including
private auxiliaries. Upstream packages cannot refer back to this project. -/
run_meta do
  let moduleNames := (← getEnv).header.moduleNames
  let forbidden := #[`FiniteSignsData.source, `FiniteRootFixture.original,
    `FiniteRootFixture.source, `FiniteRootOrdinary.source, `FiniteJoint.joint,
    ``FiniteJoint.joint, ``FiniteJoint.exists_joint, ``FiniteJoint.nextData,
    `FiniteCanonicalFormula.witness, `FiniteCanonicalFormula.matrix,
    `FiniteSourceFrozenQuoted.original, `FiniteSourceFrozenQuoted.matrix,
    `Hex.RCF.RealCoefficients.NestedTransportTests.Ordinary.source,
    `Hex.RCF.RealCoefficients.NestedRootProduceConformance.source]
  let required := #[``Data.replay, ``Data.accepted, ``Binding.bind, ``Binding.valuation_eq,
    ``Semantics.read_eq, ``Semantics.root, ``Semantics.alpha_sqrt,
    ``Hex.RCF.RealCoefficients.FiniteSigns.check_sound,
    ``Hex.RealClosure.Transport.Finite.ReplayData.of_closed,
    ``Hex.RealClosure.Transport.Inventory.replay_data,
    ``Hex.RealClosure.Algebraic.Element.denote_mul, ``Hex.SignDet.Descriptor.root_unique]
  for name in #[``Quote.original, ``Quote.guarded] do
    let .thmInfo info ← getConstInfo name | throwError "expected quoted source body"
    let _ ← Hex.RCF.checkProof name info.type info.value
    let axioms ← collectAxioms name
    unless axioms.size == 3 && axioms.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "unexpected quoted-source axiom"
    let mut pending := [name]
    let mut seen : NameHashSet := {}
    let environment ← getEnv
    while !pending.isEmpty do
      let current := pending.head!
      pending := pending.tail!
      if seen.contains current then continue
      seen := seen.insert current
      if forbidden.contains current then throwError "source reused an earlier witness: {current}"
      if let some index := environment.getModuleIdxFor? current then
        let moduleName := moduleNames[index]!
        if #[`Init, `Lean, `Std, `Batteries, `Mathlib, `Aesop, `Qq, `TauCeti].any
            (fun boundary => boundary.isPrefixOf moduleName) then continue
      let declaration ← getConstInfo current
      pending := declaration.type.getUsedConstants.toList ++ pending
      if let some body := declaration.value? (allowOpaque := true) then
        pending := body.getUsedConstants.toList ++ pending
    for requiredName in required do
      unless seen.contains requiredName do throwError "source omitted owner/checker evidence: {requiredName}"
  let environment ← getEnv
  for (name, declaration) in environment.constants do
    let belongs := if let some index := environment.getModuleIdxFor? name then
      (`HexRCF.FiniteMatrix).isPrefixOf moduleNames[index]!
    else (`Hex.RCF.RealCoefficients.FiniteMatrixTests).isPrefixOf name
    if belongs && declaration.isTheorem then
      let axioms ← collectAxioms name
      unless axioms.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
        throwError "unexpected finite-matrix theorem axiom: {name}"
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Ordinary
