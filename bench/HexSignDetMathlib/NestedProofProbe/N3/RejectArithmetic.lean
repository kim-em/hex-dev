/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.ProofProbe.Nested.Inputs
public meta import HexSignDet.Dag
public meta import HexSignDet.Replay

public section

namespace Hex.SignDetMathlib.NestedProofProbe.N3.RejectArithmetic
open Hex.SignDet Hex.SignDetMathlib.ProofProbe

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
/-- A positive forged initial scale fails the actual polynomial identity check. -/
theorem checked : Nested.check 3 false true = false := by
  simp only [Nested.check, Dag.check, Dag.replay_eq, Dag.step_eq,
    Replay.check, Node.check_eq, checkMoment_eq, queryPoly, Sturm.check,
    TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- info: 'Hex.SignDetMathlib.NestedProofProbe.N3.RejectArithmetic.checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checked

/-- Positive scale 2 passes its sign guard, but changes the initial value. -/
theorem cause : Nested.scaleFailure 3 = true := by
  decide +kernel

#print axioms cause

-- The external runner reads this unguarded inventory.
#print axioms checked
end Hex.SignDetMathlib.NestedProofProbe.N3.RejectArithmetic
