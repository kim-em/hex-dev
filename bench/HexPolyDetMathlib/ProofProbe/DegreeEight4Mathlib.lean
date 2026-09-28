/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDetMathlib
import Mathlib.Tactic.NormDet
import Mathlib.Tactic.Ring

open Matrix

theorem HexPolyDetMathlib.ProofProbe.DegreeEight4Mathlib.result (a b u : Rat) : Matrix.det !![(a+b)^8/u, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] = (a+b)^8/u := by
  simp only [norm_det] <;> ring
