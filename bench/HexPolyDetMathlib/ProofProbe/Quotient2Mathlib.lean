/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDetMathlib
import Mathlib.Tactic.NormDet
import Mathlib.Tactic.Ring

open Matrix

theorem HexPolyDetMathlib.ProofProbe.Quotient2Mathlib.result (a b c d u v w x : Rat) : Matrix.det (!![a/u, b/v; c/w, d/x] : Matrix (Fin 2) (Fin 2) Rat) = a*d/(u*x)-b*c/(v*w) := by
  simp only [norm_det] <;> ring
