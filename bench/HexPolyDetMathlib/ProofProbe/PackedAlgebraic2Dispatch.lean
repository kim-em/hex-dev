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
set_option trace.HexMatrix.certificate true
set_option hex.det.checker 0
set_option profiler true
set_option profiler.threshold 1000000

theorem result  : Matrix.det (R := ClosedAlgebraic.K) (!![ClosedAlgebraic.α, 1; 2, ClosedAlgebraic.α]) = (ClosedAlgebraic.α ^ 2 - 2) ^ 1 := by
  det

#print axioms result
