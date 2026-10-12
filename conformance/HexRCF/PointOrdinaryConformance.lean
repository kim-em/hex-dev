/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.PointProduceConformance
import HexRCF.ProofEvidence
open Lean Meta
open Hex.RCF.RealCoefficients
namespace Hex.RCF.RealCoefficients.PointOrdinaryConformance
set_option maxRecDepth 32768 in
set_option maxHeartbeats 20000000 in
theorem source : ∃ x : ℝ, 1 < x ∧ x < Real.sqrt 2 := by
  produced_point
#print axioms source
run_meta do
  let proof := mkConst ``source
  let _ ← Hex.RCF.checkProof ``source (← inferType proof) proof
  for law in #[``PointReplay.check_sound, ``ScalarPacket.restore] do
    unless ← Hex.RCF.ProofEvidence.contains ``source (fun e => e.isConstOf law) do
      throwError "ordinary point source omitted replay law"
  for producer in PointProduceConformance.producers do
    if ← Hex.RCF.ProofEvidence.contains ``source (fun e => e.isConstOf producer) then
      throwError "ordinary point source retained a producer"
  for name in #[``PointReplay.row_signs, ``PointReplay.checkWith_eq,
      ``PointReplay.check_fields, ``PointReplay.check_domains,
      ``PointReplay.check_sound, ``PointReplay.check_false, ``PointReplay.check_zero, ``source] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "point replay has a forbidden axiom"
end Hex.RCF.RealCoefficients.PointOrdinaryConformance
