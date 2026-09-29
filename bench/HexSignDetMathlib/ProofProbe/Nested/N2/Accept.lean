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

namespace Hex.SignDetMathlib.ProofProbe.Nested.N2.Accept
open Hex.SignDet

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
/-- Ordinary-kernel replay of supplied values and complete literal query chains. -/
theorem checked : Nested.check 2 = true := by
  simp only [Nested.check, Dag.check, Dag.replay_eq, Dag.step_eq,
    Replay.check, Node.check_eq, checkMoment_eq, queryPoly, Sturm.check,
    TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- info: 'Hex.SignDetMathlib.ProofProbe.Nested.N2.Accept.checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checked

#print axioms checked
end Hex.SignDetMathlib.ProofProbe.Nested.N2.Accept
