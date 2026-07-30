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
theorem sortedAddition64 :
    sortedAdditionLex 64 ∧ sortedAdditionGrevlex 64 := by
  unfold sortedAdditionLex sortedAdditionGrevlex
  decide +kernel

#print axioms sortedAddition64

end HexMvPolyMathlib.ProofProbe
