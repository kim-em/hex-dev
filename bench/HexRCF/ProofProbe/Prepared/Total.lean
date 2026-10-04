/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.ProofProbe.Prepared.Support
public meta import HexRCF.ProofEvidence
public section

namespace Hex.RCF.ProofProbe.Prepared.Total
open Hex.RCF.ProofProbe.Prepared
set_option maxRecDepth 8192
set_option maxHeartbeats 2400000
set_option rcf.algebraic.directDepth 0

theorem goal : ∃ x ∈ Set.Ioc (1 : ℝ) 2, x ^ 2 = Real.sqrt 2 := by prepared_total

run_meta do
  unless ← Hex.RCF.ProofEvidence.contains `Hex.RCF.ProofProbe.Prepared.Total.goal
      (fun e => e.isConstOf ``Hex.RCF.RealCoefficients.Replay.check_sound) do
    throwError "total production probe did not quote finite replay"
  for name in [``Hex.RCF.RealCoefficients.Replay.buildTotal,
      ``Hex.RCF.RealCoefficients.FieldBuild.produce,
      ``Hex.RCF.RealCoefficients.Field.prepareSign, ``Hex.Sturm.queryPrepared,
      ``Hex.Sturm.certifyPrepared, ``Hex.RCF.RealCoefficients.FieldBuild.buildTable] do
    if ← Hex.RCF.ProofEvidence.contains `Hex.RCF.ProofProbe.Prepared.Total.goal
        (fun e => e.isConstOf name) then
      throwError "total production entered the quoted proof"

/-- info: 'Hex.RCF.ProofProbe.Prepared.Total.goal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms goal

end Hex.RCF.ProofProbe.Prepared.Total
