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
theorem sortedAddition32 :
    sortedAdditionLex 32 ∧ sortedAdditionGrevlex 32 := by
  unfold sortedAdditionLex sortedAdditionGrevlex
  decide +kernel

#print axioms sortedAddition32

end HexMvPolyMathlib.ProofProbe
