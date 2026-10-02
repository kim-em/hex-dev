/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.Diagnostics.Nested.Inputs
public meta import HexSignDet.Dag
public meta import HexSignDet.Replay

public section

namespace Hex.SignDetMathlib.Diagnostics.DepthThree.N3.ArithmeticCause
open Hex.SignDet Hex.SignDetMathlib.Diagnostics

set_option maxRecDepth 65536 in
set_option maxHeartbeats 4000000 in
/-- The forged certificate fails its initial identity after all preceding chain guards pass. -/
theorem checked : Nested.scaleFailure 3 = true := by
  simp only [Nested.scaleFailure, SignedRemainderChain.check,
    ← Array.all_toList, Array.toList_range]
  decide +kernel

/-- info: 'Hex.SignDetMathlib.Diagnostics.DepthThree.N3.ArithmeticCause.checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms checked

end Hex.SignDetMathlib.Diagnostics.DepthThree.N3.ArithmeticCause
