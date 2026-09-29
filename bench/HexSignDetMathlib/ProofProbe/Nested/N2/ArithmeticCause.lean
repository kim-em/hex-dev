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

namespace Hex.SignDetMathlib.ProofProbe.Nested.N2.ArithmeticCause
open Hex.SignDet Hex.SignDetMathlib.ProofProbe

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
/-- The forged certificate fails its initial identity after all preceding guards pass. -/
theorem checked : Nested.scaleFailure 2 = true := by
  simp only [Nested.scaleFailure, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- info: 'Hex.SignDetMathlib.ProofProbe.Nested.N2.ArithmeticCause.checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checked

-- The external runner reads this unguarded inventory.
#print axioms checked
end Hex.SignDetMathlib.ProofProbe.Nested.N2.ArithmeticCause
