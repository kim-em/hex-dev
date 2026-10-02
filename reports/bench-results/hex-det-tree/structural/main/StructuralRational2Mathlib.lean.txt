/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexPolyDetMathlib.Tactic
import Mathlib.Tactic.NormDet
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option trace.HexMatrix.certificate false
set_option profiler false

namespace HexPolyDetMathlib.ProofProbe.StructuralRational2Mathlib
theorem result (x0 : Rat) : Matrix.det (R := Rat) (!![x0/2, 1; 1, x0/3]) = x0^2/6-1 := by
  simp only [norm_det] <;> ring
end HexPolyDetMathlib.ProofProbe.StructuralRational2Mathlib
