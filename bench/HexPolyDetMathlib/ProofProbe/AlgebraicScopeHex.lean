/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDetMathlib.Tactic
import HexPolyDetMathlib.ProofProbe.AlgebraicSupport

theorem result : Matrix.det !![ClosedAlgebraic.α, 1; 2, ClosedAlgebraic.α] = 0 := by
  fail_if_success (solve | det)
  rw [Matrix.det_fin_two]
  change ClosedAlgebraic.α * ClosedAlgebraic.α - 1 * 2 = 0
  rw [← pow_two, ClosedAlgebraic.square, one_mul, sub_self]
#print axioms result
