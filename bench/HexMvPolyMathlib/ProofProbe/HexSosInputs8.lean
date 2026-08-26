/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPolyMathlib.ProofProbe.Support

public section

namespace HexMvPolyMathlib.ProofProbe

set_option maxHeartbeats 32000000 in
theorem hexSosInputs8 : hexSosInputs 8 := by
  unfold hexSosInputs
  decide +kernel

#print axioms hexSosInputs8

end HexMvPolyMathlib.ProofProbe
