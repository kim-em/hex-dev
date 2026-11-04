/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.SuppliedIrreducible
public import HexRCF.RealCoefficients
public import HexRCF.CertificationInputs
-- The explicit certificate API still needs the scoped instance. Automatic
-- finite replay must remain independent of that extra common-field proof.
public import HexRCF.CertificationProofs
public meta import HexRCF.CertificationInputs
public meta import HexRCF.RealCoefficients
public meta import HexRCF.ProofEvidence
public meta import HexRCF.FiniteEvidence
public meta import Lean.Elab.Command
public section
open Hex Hex.RCF Hex.RCF.RealCoefficients Lean Meta Qq
namespace Hex.RCF.SuppliedIrreducibleProofs
set_option maxRecDepth 32768

run_meta do
  let p : ZPoly := DensePoly.ofList [-2,-24,169,70,-127,-70,6,8,1]
  let expression : Q(ZPoly) ← FieldLiteral.zpolyExpr p
  let target ← mkAppM ``ZPoly.CheckedIrreducible #[expression]
  unless (← synthInstance? target).isNone do
    throwError "supplied instance escaped its scope"

open scoped Hex.RCF.SuppliedIrreducible

theorem positive : ∀ x : ℝ,
    x ^ 2 + CertificationInputs.realAlgebraic.toReal + Real.sqrt 2 > 0 := by rcf

/-- info: 'Hex.RCF.SuppliedIrreducibleProofs.positive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms positive
run_meta do
  if ← Hex.RCF.ProofEvidence.contains ``positive
      (fun e => e.isConstOf ``Hex.RCF.SuppliedIrreducible.supplied) then
    throwError "finite replay quoted the supplied common-field instance"
  unless ← Hex.RCF.ProofEvidence.contains ``positive
      (fun e => e.isConstOf ``FieldCells.forall_formula) do
    throwError "automatic proof omitted finite cell replay"

set_option maxHeartbeats 8000000 in
run_meta do
  let target := (← getConstInfo ``positive).type
  let .ok prepared ← Coefficients.prepare target |
    throwError "explicit legacy preparation declined its supplied instance"
  let proof ← prepared.prove
  addDecl (.thmDecl {
    name := `Hex.RCF.SuppliedIrreducibleProofs.legacyPositive
    levelParams := [], type := target, value := proof })
  let rejected ← try
    let _ ← FiniteEvidence.checkClasses `Hex.RCF.SuppliedIrreducibleProofs.legacyPositive
      #[CertificationInputs.polynomial,SquareTwo.polynomial] #[8]
    pure none
  catch error => pure (some (← error.toMessageData.toString))
  unless rejected.any (fun message =>
      (message.splitOn "quotes irreducibility of a non-source presentation").length > 1) do
    throwError "the own-presentation audit missed the explicit common-field class: {rejected}"

#print axioms Hex.RCF.SuppliedIrreducibleProofs.legacyPositive

run_meta do
  let p : ZPoly := DensePoly.ofList [-2,-24,169,70,-127,-70,6,8,1]
  let expression : Q(ZPoly) ← FieldLiteral.zpolyExpr p
  let degree ← mkDecideProof q(0 < ($expression).natDegree)
  let checked ← CommonTactic.certify p expression degree
  Hex.RCF.checkAxioms `Hex.RCF.SuppliedIrreducibleProofs.accepted checked
  unless ← Hex.RCF.ProofEvidence.contains checked.getAppFn.constName!
      (fun e => e.isConstOf ``Hex.RCF.SuppliedIrreducible.supplied) do
    throwError "direct certification did not consume supplied irreducibility"

run_meta do
  let p : ZPoly := DensePoly.ofList [-2,-24,169,70,-127,-70,6,8,1]
  let expression : Q(ZPoly) ← FieldLiteral.zpolyExpr p
  let degree ← mkDecideProof q(0 < ($expression).natDegree)
  let saved ← saveState
  let rejected ← try
    let _ ← CommonTactic.certify
      (DensePoly.ofList [-3,-24,169,70,-127,-70,6,8,1]) expression degree
    pure none
  catch error => pure (some (← error.toMessageData.toString))
  saved.restore
  unless rejected == some "rcf: irreducibility proof has a different runtime polynomial" do
    throwError "unexpected runtime binding result: {rejected}"

run_meta do
  let p : ZPoly := DensePoly.ofList [-2,-7,-1,4,1]
  let expression : Q(ZPoly) ← FieldLiteral.zpolyExpr p
  let target ← mkAppM ``ZPoly.CheckedIrreducible #[expression]
  let degree ← mkDecideProof q(0 < ($expression).natDegree)
  let saved ← saveState
  let rejected ← try
    let _ ← withLetDecl `forged target (← mkSorry target false) fun forged =>
      withNewLocalInstances #[forged] 0 <| CommonTactic.certify p expression degree
    pure none
  catch error => pure (some (← error.toMessageData.toString))
  saved.restore
  let some message := rejected | throwError "admitted supplied proof triggered certificate fallback"
  unless message.startsWith "rcf: supplied CheckedIrreducible instance for " &&
      (message.splitOn "forbidden axiom sorryAx").length > 1 do
    throwError "unexpected supplied proof rejection: {message}"
  let valid ← CommonTactic.certify p expression degree
  Hex.RCF.checkAxioms `Hex.RCF.SuppliedIrreducibleProofs.restored valid

end Hex.RCF.SuppliedIrreducibleProofs
