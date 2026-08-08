/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPolyMathlib.ProofProbe.Support

public section

namespace HexMvPolyMathlib.ProofProbe

set_option maxHeartbeats 4000000 in
theorem hexMulCollideInputs8 : hexMulCollideInputs 8 := by
  unfold hexMulCollideInputs
  decide +kernel

#print axioms hexMulCollideInputs8

end HexMvPolyMathlib.ProofProbe
