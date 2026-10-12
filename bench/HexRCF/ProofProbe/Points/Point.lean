/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.SectionProduceConformance
import HexRCF.PointProduceConformance
import HexRCF.ProofEvidence
open Lean Meta
open Hex.RCF.RealCoefficients
namespace Hex.RCF.ProofProbe.Points.Point
set_option maxRecDepth 32768 in
set_option maxHeartbeats 20000000 in
theorem witness : ∃ x : ℝ, x = Real.sqrt 2 := by
  produced_point
#print axioms witness
run_meta do
  unless ← Hex.RCF.ProofEvidence.contains ``witness
      (fun e => e.isConstOf ``PointReplay.check_sound) do
    throwError "point selection cost probe omitted its replay law"
  for producer in PointProduceConformance.producers do
    if ← Hex.RCF.ProofEvidence.contains ``witness (fun e => e.isConstOf producer) then
      throwError "point selection cost probe retained native production"
end Hex.RCF.ProofProbe.Points.Point
