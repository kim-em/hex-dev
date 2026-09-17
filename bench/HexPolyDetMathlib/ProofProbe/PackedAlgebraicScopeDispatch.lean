/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDetMathlib.Tactic
import HexPolyDetMathlib.ProofProbe.AlgebraicSupport

set_option trace.HexMatrix.certificate true
set_option hex.det.checker 0
set_option profiler true
set_option profiler.threshold 1000000

theorem result : Matrix.det !![ClosedAlgebraic.α, 1; 2, ClosedAlgebraic.α] = 0 := by
  fail_if_success (solve | det)
  rw [Matrix.det_fin_two]
  change ClosedAlgebraic.α * ClosedAlgebraic.α - 1 * 2 = 0
  rw [← pow_two, ClosedAlgebraic.square, one_mul, sub_self]
#print axioms result
