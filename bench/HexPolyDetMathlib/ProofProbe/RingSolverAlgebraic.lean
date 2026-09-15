/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Tactic
import HexPolyDetMathlib.ProofProbe.AlgebraicSupport

theorem result (h : ClosedAlgebraic.α ^ 2 = 2) :
    ClosedAlgebraic.α * ClosedAlgebraic.α - 1 * 2 = 0 := by
  grobner

#print axioms result
