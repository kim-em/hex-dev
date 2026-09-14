/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDetMathlib.Tactic
import HexPolyDetMathlib.ProofProbe.AlgebraicSupport

set_option maxHeartbeats 0
set_option maxRecDepth 100000

-- Computational performance owner: HexPolyDet.
theorem result  : Matrix.det (R := ClosedAlgebraic.K) !![ClosedAlgebraic.α, 1, 0, 0; 2, ClosedAlgebraic.α, 0, 0; 0, 0, ClosedAlgebraic.α, 1; 0, 0, 2, ClosedAlgebraic.α] = (ClosedAlgebraic.α ^ 2 - 2) ^ 2 := by
  det

#print axioms result
