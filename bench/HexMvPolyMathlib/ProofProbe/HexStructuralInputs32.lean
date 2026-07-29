/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPolyMathlib.ProofProbe.Support

public section

namespace HexMvPolyMathlib.ProofProbe

set_option maxHeartbeats 16000000 in
theorem hexStructuralInputs32 : hexStructuralInputs 32 := by
  unfold hexStructuralInputs
  decide +kernel

#print axioms hexStructuralInputs32

end HexMvPolyMathlib.ProofProbe
