/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetTheory.Diagnostics.Inputs

public section

namespace Hex.SignDetTheory.Diagnostics.D5.Reject
open Hex.SignDet Hex.SignDetTheory.Diagnostics.Inputs

@[expose] def evidence : Dag Rat Nat := stale 5

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
/-- Ordinary-kernel replay of the supplied graph expression. -/
theorem checked : check 5 evidence = false := by
  simp only [check, Dag.check, Dag.replay_eq, Dag.step_eq, evidence, stale, entries,
    Replay.check, Node.check_eq, checkMoment_eq, queryPoly, Sturm.check,
    TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- info: 'Hex.SignDetTheory.Diagnostics.D5.Reject.checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms checked

end Hex.SignDetTheory.Diagnostics.D5.Reject
