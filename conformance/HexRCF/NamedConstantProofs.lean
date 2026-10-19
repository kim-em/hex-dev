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
set_option maxHeartbeats 12000000

run_meta do
  let examples := #[( ``NamedConstants.pi_square, ``NamedConstants.piRegistration),
    (``NamedConstants.exp_square, ``NamedConstants.expRegistration),
    (``NamedConstants.exp_witness, ``NamedConstants.expRegistration),
    (``NamedConstants.pi_inverse, ``NamedConstants.piRegistration)]
  for (name, registration) in examples do
    let dependencies ← Hex.RCF.ProofEvidence.projectDependencies #[name]
    unless dependencies.contains registration do
      throwError "named-constant proof omitted its supplied registration: {name}"
  let axioms ← Algebraic.KernelReplay.AxiomClosure.collect (examples.map Prod.fst)
  unless axioms == (#[``propext,``Classical.choice,``Quot.sound].qsort Name.lt) do
    throwError "unexpected complete named-constant axiom closure: {axioms}"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies (examples.map Prod.fst)
  let some index := (← getEnv).getModuleIdxFor? examples[0]!.1
    | throwError "named-constant proof module missing"
  let mut checked : Nat := 0
  let mut inventory : Array Name := #[]
  for name in dependencies.toArray do
    if (← getEnv).getModuleIdxFor? name == some index then
      if let .thmInfo declaration ← getConstInfo name then
        let _ ← Hex.RCF.checkProof name declaration.type declaration.value
        checked := checked+1
        inventory := inventory.push name
  unless checked == 42 do throwError "named-constant body coverage changed: {checked}"
  logInfo m!"four imported pi/e goals: {checked} actual module-local theorem bodies rechecked, including auxiliaries; supplied registrations and complete standard-three axiom closure verified"
  logInfo m!"named theorem inventory: {inventory.qsort Name.lt}"

end Hex.RCF.NamedConstantProofs
