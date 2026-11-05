/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.CertificationInputs
public meta import HexRCF.CertificationInputs
public meta import HexRCF.RealCoefficients.CommonTactic
public meta import Lean.Elab.Command
public section
open Hex Hex.RCF Hex.RCF.RealCoefficients Lean Meta Qq
set_option maxRecDepth 32768
set_option maxHeartbeats 40000000
set_option debug.skipKernelTC false
set_option Elab.async false
run_meta do
  let alpha : Q(ℝ) := q(Hex.RCF.CertificationInputs.realAlgebraic.toReal)
  let cases : Array (Name × Expr × Nat) := #[
    (`Hex.RCF.FiniteNestedSources.octicBase,q(∀ x : ℝ, x^2+Real.sqrt ($alpha+Real.sqrt 2)>0),0),
    (`Hex.RCF.FiniteNestedSources.guardedBase,q(∀ x : ℝ, x^2+Real.sqrt (1/(Real.sqrt 2+1))>0),1)]
  for (name,target,guards) in cases do
    let .ok prepared ← CommonTactic.prepareCoordinates target |
      throwError "nested source preparation declined {name}"
    unless prepared.source.divisors.size == guards do throwError "nested source lost original guards"
    let proof ← prepared.prove
    let proof ← Hex.RCF.checkProof name target proof
    addDecl (.thmDecl {name,levelParams:=[],type:=target,value:=proof})
    logInfo m!"FINITE_NESTED_SOURCE {name}: degree={prepared.polynomial.natDegree}; guards={guards}; original target checked"
#print axioms Hex.RCF.FiniteNestedSources.octicBase
#print axioms Hex.RCF.FiniteNestedSources.guardedBase
