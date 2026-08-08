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
theorem sortedSosInputs6 : sortedSosInputs 6 := by
  unfold sortedSosInputs
  decide +kernel

#print axioms sortedSosInputs6

end HexMvPolyMathlib.ProofProbe
