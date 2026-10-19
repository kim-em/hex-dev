/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients
import HexRCF.SectionProduceConformance
import HexRCF.ProofEvidence

namespace Hex.RCF.RealCoefficients.SectionOrdinaryConformance

set_option maxRecDepth 32768 in
set_option maxHeartbeats 20000000 in
theorem witness : ∃ x : ℝ, x^2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 := by
  produced_section

/-- info: 'Hex.RCF.RealCoefficients.SectionOrdinaryConformance.witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms witness

run_meta do
  let proof := Lean.mkConst ``witness
  let _ ← Hex.RCF.checkProof ``witness (← Lean.Meta.inferType proof) proof
  for law in #[``SectionReplay.check_sound, ``ScalarPacket.restore] do
    unless ← Hex.RCF.ProofEvidence.contains ``witness (fun e => e.isConstOf law) do
      Lean.throwError "fresh quotation omitted its section or scalar replay law"
  for producer in SectionProduceConformance.producers do
    if ← Hex.RCF.ProofEvidence.contains ``witness (fun e => e.isConstOf producer) then
      Lean.throwError "fresh quotation retains a producer"
  let axioms ← Lean.collectAxioms ``witness
  unless axioms.size == 3 && axioms.all
      (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
    Lean.throwError "fresh quotation has an unexpected complete inventory"

end Hex.RCF.RealCoefficients.SectionOrdinaryConformance
