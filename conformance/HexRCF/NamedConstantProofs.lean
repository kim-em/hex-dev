/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.NamedConstants
import HexRCF.ProofEvidence
import KernelReplay.AxiomClosure

open Lean Meta Hex Hex.RealClosure
namespace Hex.RCF.NamedConstantProofs
set_option maxRecDepth 32768

run_meta do
  let examples := #[( ``NamedConstants.pi_square, ``NamedConstants.piRegistration),
    (``NamedConstants.exp_square, ``NamedConstants.expRegistration),
    (``NamedConstants.exp_witness, ``NamedConstants.expRegistration),
    (``NamedConstants.pi_inverse, ``NamedConstants.piRegistration)]
  for (name, registration) in examples do
    let .thmInfo declaration ← getConstInfo name | throwError "named-constant proof missing: {name}"
    let _ ← Hex.RCF.checkProof name declaration.type declaration.value
    let dependencies ← Hex.RCF.ProofEvidence.projectDependencies #[name]
    unless dependencies.contains registration do
      throwError "named-constant proof omitted its supplied registration: {name}"
  let axioms ← Algebraic.KernelReplay.AxiomClosure.collect (examples.map Prod.fst)
  unless axioms == (#[``propext,``Classical.choice,``Quot.sound].qsort Name.lt) do
    throwError "unexpected complete named-constant axiom closure: {axioms}"
  logInfo "four imported pi/e tactic proof bodies rechecked; actual supplied registrations and complete standard-three axiom closure verified"

end Hex.RCF.NamedConstantProofs
