/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.MaximalCoefficients
import HexRCF.MaximalCoefficientsConformance
import HexRCF.RegisteredConstants
import KernelReplay.AxiomClosure

set_option maxHeartbeats 5000000
set_option maxRecDepth 32768

example : True := Hex.RCF.MaximalCoefficientsConformance.proofsComplete

open Lean Meta in
run_meta do
  let names := #[``Hex.RCF.RealCoefficients.MaximalCoefficientsTests.metadataBare,
    ``Hex.RCF.RealCoefficients.MaximalCoefficientsTests.metadataDedup,
    ``Hex.RCF.MaximalCoefficientsConformance.sum_positive,
    ``Hex.RCF.MaximalCoefficientsConformance.square_positive,
    ``Hex.RCF.MaximalCoefficientsConformance.negative_witness,
    ``Hex.RCF.RegisteredConstants.positiveSquaredCoefficient,
    ``Hex.RCF.RegisteredConstants.squareWitness,
    ``Hex.RCF.RegisteredConstants.intervalWitness,
    ``Hex.RCF.RegisteredConstants.nestedWitness,
    ``Hex.RCF.RegisteredConstants.quotientWitness,
    ``Hex.RCF.RegisteredConstants.inverseWitness,
    ``Hex.RCF.RegisteredConstants.halfWitness,
    ``Hex.RCF.RegisteredConstants.compoundEquality,
    ``Hex.RCF.RegisteredConstants.reorderedWitness,
    ``Hex.RCF.RegisteredConstants.reversedWitness,
    ``Hex.RCF.RegisteredConstants.aliasedWitness,
    `Hex.RCF.RegisteredConstants.metadataWitness]
  for name in names do
    let .thmInfo declaration ← getConstInfo name | throwError "missing maximal coefficient theorem"
    let _ ← Hex.RCF.checkProof name declaration.type declaration.value
  let axioms ← Hex.RealClosure.Algebraic.KernelReplay.AxiomClosure.collect names
  unless axioms == (#[``propext, ``Classical.choice, ``Quot.sound].qsort Name.lt) do
    throwError "maximal coefficient checked-body axiom closure changed"
  let direct ← Hex.RCF.ProofEvidence.projectDependencies
    #[``Hex.RCF.RealCoefficients.MaximalCoefficientsTests.metadataBare]
  unless direct.contains ``Hex.RCF.RealCoefficients.SquareTwo.valuation do
    throwError "metadata proof omitted the direct algebraic handler"
  -- Both frontends use FieldBuild's soundness theorem. SquareTwo.valuation
  -- is emitted only by the direct frontend and distinguishes this route.
  unless direct.contains ``Hex.RCF.RealCoefficients.FieldBuild.Result.checkForall_sound do
    throwError "metadata proof omitted the shared ordinary field checker"
  for name in #[``Hex.RCF.RegisteredConstants.squareWitness,
      ``Hex.RCF.RegisteredConstants.intervalWitness, ``Hex.RCF.RegisteredConstants.nestedWitness,
      ``Hex.RCF.RegisteredConstants.quotientWitness, ``Hex.RCF.RegisteredConstants.inverseWitness,
      ``Hex.RCF.RegisteredConstants.halfWitness, ``Hex.RCF.RegisteredConstants.compoundEquality] do
    let dependencies ← Hex.RCF.ProofEvidence.projectDependencies #[name]
    unless dependencies.contains ``Hex.RCF.RegisteredConstants.suppliedRegistration do
      throwError "registered witness bypassed its supplied containment evidence"
  logInfo "fresh closed-sum, square and negative-witness bodies have only the standard three axioms"
  logInfo "fresh registered square-bound and both equality-witness orientations checked"
