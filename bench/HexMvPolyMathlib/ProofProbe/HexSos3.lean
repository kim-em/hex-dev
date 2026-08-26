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
theorem hexSos3 : hexSos 3 := by
  unfold hexSos
  decide +kernel

#print axioms hexSos3

end HexMvPolyMathlib.ProofProbe
