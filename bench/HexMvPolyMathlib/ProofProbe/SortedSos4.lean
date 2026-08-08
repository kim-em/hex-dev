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
theorem sortedSos4 : sortedSos 4 := by
  unfold sortedSos
  decide +kernel

#print axioms sortedSos4

end HexMvPolyMathlib.ProofProbe
