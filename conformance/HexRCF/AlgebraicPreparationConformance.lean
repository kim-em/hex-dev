/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.AlgebraicPreparationCases
import KernelReplay.AxiomClosure
import HexRCF.ProofEvidence
open Lean Meta

-- A separate importing module requires the end-of-run marker. A swallowed
-- test interrupt must not leave an apparently green, partially executed run.
run_meta do
  let .thmInfo declaration ← getConstInfo ``Hex.RCF.AlgebraicPreparationConformance.runFinished
    | throwError "native source conformance did not finish"
  let _ ← Hex.RCF.checkProof `nativeSourceRunCompleted declaration.type declaration.value
  logInfo "native source conformance completion independently checked"

run_meta do
  let names := #[`rationalAcceptance, `algebraicAcceptance, `falseAcceptance,
    `divisorAcceptance, `zeroGuardAcceptance, `emptyDomainAcceptance].map
      (`Hex.RCF.AlgebraicPreparationConformance ++ ·)
  for name in names do
    let .thmInfo declaration ← getConstInfo name | throwError "source acceptance consumer is missing"
    let _ ← Hex.RCF.checkProof name declaration.type declaration.value
  let axioms ← Hex.RealClosure.Algebraic.KernelReplay.AxiomClosure.collect names
  unless axioms == (#[``propext, ``Classical.choice, ``Quot.sound].qsort Name.lt) do
    throwError "source acceptance has an unexpected complete axiom closure"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies names
  for name in #[``Hex.RCF.RealCoefficients.AlgebraicCells.accepts_iff,
      ``Hex.RCF.RealCoefficients.AlgebraicCells.build_complete,
      ``Hex.RCF.RealCoefficients.AlgebraicCells.build_domains] do
    unless dependencies.contains name do throwError "source acceptance omitted an actual owner law"
  logInfo "fresh source acceptance bodies retain original domains and actual complete production laws with the standard three axioms"
