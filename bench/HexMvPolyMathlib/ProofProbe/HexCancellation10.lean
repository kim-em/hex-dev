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
theorem hexCancellation10 :
    hexCancellationInt 10 ∧ hexCancellationRat 10 := by
  unfold hexCancellationInt hexCancellationRat
  decide +kernel

#print axioms hexCancellation10

end HexMvPolyMathlib.ProofProbe
