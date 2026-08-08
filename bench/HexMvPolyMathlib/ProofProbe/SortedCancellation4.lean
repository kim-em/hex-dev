/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMvPolyMathlib.ProofProbe.Support

public section

namespace HexMvPolyMathlib.ProofProbe

set_option maxHeartbeats 2000000 in
theorem sortedCancellation4 :
    sortedCancellationInt 4 ∧ sortedCancellationRat 4 := by
  unfold sortedCancellationInt sortedCancellationRat
  decide +kernel

#print axioms sortedCancellation4

end HexMvPolyMathlib.ProofProbe
