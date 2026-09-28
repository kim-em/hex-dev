/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDetMathlib
import Mathlib.Tactic.NormDet
import Mathlib.Tactic.Ring

open Matrix

def HexPolyDetMathlib.ProofProbe.ResultSymbolic3Mathlib.certificate (x : Int) : {d : Int // Matrix.det (!![x, 1, 0; 1, x, 1; 0, 1, x] : Matrix (Fin 3) (Fin 3) Int) = d} := by
  refine ⟨?_, ?_⟩
  rotate_left
  simp only [norm_det]
  rfl
