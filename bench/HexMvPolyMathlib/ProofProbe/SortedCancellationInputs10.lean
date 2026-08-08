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
theorem sortedCancellationInputs10 : sortedCancellationInputs 10 := by
  unfold sortedCancellationInputs
  decide +kernel

#print axioms sortedCancellationInputs10

end HexMvPolyMathlib.ProofProbe
