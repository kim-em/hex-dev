/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.MaximalCoefficientsConformance
import HexRCF.RegisteredConstants
import KernelReplay.AxiomClosure

set_option maxHeartbeats 5000000
set_option maxRecDepth 32768

example : True := Hex.RCF.MaximalCoefficientsConformance.proofsComplete

open Lean Meta in
run_meta do
  let names := #[``Hex.RCF.MaximalCoefficientsConformance.sum_positive,
    ``Hex.RCF.MaximalCoefficientsConformance.square_positive,
    ``Hex.RCF.MaximalCoefficientsConformance.negative_witness,
    ``Hex.RCF.RegisteredConstants.positiveSquaredCoefficient,
    ``Hex.RCF.RegisteredConstants.reorderedWitness,
    ``Hex.RCF.RegisteredConstants.reversedWitness]
  for name in names do
    let .thmInfo declaration ← getConstInfo name | throwError "missing maximal coefficient theorem"
    let _ ← Hex.RCF.checkProof name declaration.type declaration.value
  let axioms ← Hex.RealClosure.Algebraic.KernelReplay.AxiomClosure.collect names
  unless axioms == (#[``propext, ``Classical.choice, ``Quot.sound].qsort Name.lt) do
    throwError "maximal coefficient checked-body axiom closure changed"
  logInfo "fresh closed-sum, square and negative-witness bodies have only the standard three axioms"
  logInfo "fresh registered square-bound and both equality-witness orientations checked"
