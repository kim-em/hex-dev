/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.ProofProbe.Inputs

public section

namespace Hex.SignDetMathlib.ProofProbe.D7.Accept
open Hex.SignDet Hex.SignDetMathlib.ProofProbe.Inputs

@[expose] def evidence : Dag Rat Nat := graph 7

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
/-- Fresh ordinary-kernel replay of the supplied graph expression. -/
theorem checked : check 7 evidence = true := by
  simp only [check, Dag.check, Dag.replay_eq, Dag.step_eq, evidence, graph, entries,
    Replay.check, Node.check_eq, checkMoment_eq, queryPoly, Sturm.check,
    TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- info: 'Hex.SignDetMathlib.ProofProbe.D7.Accept.checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checked

#print axioms checked

end Hex.SignDetMathlib.ProofProbe.D7.Accept
