/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Tactic.NormDet
import Mathlib.Tactic.Ring
import HexPolyDetMathlib.ProofProbe.GeneralSupport

open Matrix

private def certificate (x : Int) : {d : Int // Matrix.det (HexPolyDetMathlib.ProofProbe.quadratic x) = d} := by
  refine ⟨?_, ?_⟩
  rotate_left
  simp only [HexPolyDetMathlib.ProofProbe.quadratic, norm_det]
  rfl

#print axioms certificate
