/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.SuppliedIrreducible
public import HexRCF.RealCoefficients
public import HexRCF.CertificationInputs
public meta import HexRCF.CertificationInputs
public meta import HexRCF.RealCoefficients
public meta import HexRCF.ProofEvidence
public meta import Lean.Elab.Command
public section
open Hex Hex.RCF Hex.RCF.RealCoefficients Lean Meta Qq
namespace Hex.RCF.SuppliedIrreducibleProofs
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

theorem positive : ∀ x : ℝ,
    x ^ 2 + CertificationInputs.realAlgebraic.toReal + Real.sqrt 2 > 0 := by rcf

/-- info: 'Hex.RCF.SuppliedIrreducibleProofs.positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms positive
run_meta do
  unless ← Hex.RCF.ProofEvidence.contains ``positive
      (fun e => e.isConstOf ``Hex.RCF.SuppliedIrreducible.supplied) do
    throwError "proof did not consume supplied common-field irreducibility"

run_meta do
  let p : ZPoly := DensePoly.ofList [-2,-24,169,70,-127,-70,6,8,1]
  let expression : Q(ZPoly) ← FieldLiteral.zpolyExpr p
  let degree ← mkDecideProof q(0 < ($expression).natDegree)
  let checked ← CommonTactic.certify p expression degree
  Hex.RCF.checkAxioms `Hex.RCF.SuppliedIrreducibleProofs.accepted checked

run_meta do
  let p : ZPoly := DensePoly.ofList [-2,-24,169,70,-127,-70,6,8,1]
  let expression : Q(ZPoly) ← FieldLiteral.zpolyExpr p
  let degree ← mkDecideProof q(0 < ($expression).natDegree)
  let saved ← saveState
  let rejected ← observing? <| CommonTactic.certify
    (DensePoly.ofList [-3,-24,169,70,-127,-70,6,8,1]) expression degree
  saved.restore
  unless rejected.isNone do throwError "mismatched runtime polynomial accepted"

run_meta do
  let p : ZPoly := DensePoly.ofList [-2,-7,-1,4,1]
  let expression : Q(ZPoly) ← FieldLiteral.zpolyExpr p
  let target ← mkAppM ``ZPoly.CheckedIrreducible #[expression]
  let degree ← mkDecideProof q(0 < ($expression).natDegree)
  let saved ← saveState
  let rejected ← observing? <| withLetDecl `forged target (← mkSorry target false) fun forged =>
    withNewLocalInstances #[forged] 0 <| CommonTactic.certify p expression degree
  saved.restore
  unless rejected.isNone do throwError "admitted supplied proof triggered certificate fallback"
  let valid ← CommonTactic.certify p expression degree
  Hex.RCF.checkAxioms `Hex.RCF.SuppliedIrreducibleProofs.restored valid

end Hex.RCF.SuppliedIrreducibleProofs
