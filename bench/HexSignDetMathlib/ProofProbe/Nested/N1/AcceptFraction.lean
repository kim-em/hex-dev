/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.ProofProbe.Nested.Fractions
public meta import HexSignDet.Dag
public meta import HexSignDet.Replay

public section

namespace Hex.SignDetMathlib.ProofProbe.Nested.N1.AcceptFraction
open Hex.SignDet

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
/-- Kernel replay with a nonunit fraction denominator. -/
theorem checked : Fractions.check = true := by
  simp only [Fractions.check, Dag.check, Dag.replay_eq, Dag.step_eq,
    Replay.check, Node.check_eq, checkMoment_eq, queryPoly, Sturm.check,
    TarskiCertificate.check_eq, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- info: 'Hex.SignDetMathlib.ProofProbe.Nested.N1.AcceptFraction.checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checked

-- The external runner reads this unguarded inventory.
#print axioms checked
end Hex.SignDetMathlib.ProofProbe.Nested.N1.AcceptFraction
