/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDetMathlib
import Mathlib.Tactic.NormDet
import Mathlib.Tactic.Ring
import HexPolyDetMathlib.ProofProbe.GeneralSupport

open Matrix

def HexPolyDetMathlib.ProofProbe.ResultTridiagonal4Mathlib.certificate (x : Int) : {d : Int // Matrix.det (HexPolyDetMathlib.ProofProbe.tridiagonal x) = d} := by
  refine ⟨?_, ?_⟩
  rotate_left
  simp only [HexPolyDetMathlib.ProofProbe.tridiagonal, norm_det]
  rfl
