/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDetMathlib
import Mathlib.Tactic.NormDet
import Mathlib.Tactic.Ring

open Matrix

def HexPolyDetMathlib.ProofProbe.ResultNumeric2Mathlib.certificate : {d : Int // Matrix.det (!![(1 : Int), 2; 3, 4] : Matrix (Fin 2) (Fin 2) Int) = d} := by
  refine ⟨?_, ?_⟩
  rotate_left
  simp only [norm_det]
  rfl
