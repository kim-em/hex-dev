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
theorem hexAddition64 :
    hexAdditionLex 64 ∧ hexAdditionGrevlex 64 := by
  unfold hexAdditionLex hexAdditionGrevlex
  decide +kernel

#print axioms hexAddition64

end HexMvPolyMathlib.ProofProbe
