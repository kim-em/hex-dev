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
theorem hexCancellationInputs10 : hexCancellationInputs 10 := by
  unfold hexCancellationInputs
  decide +kernel

#print axioms hexCancellationInputs10

end HexMvPolyMathlib.ProofProbe
