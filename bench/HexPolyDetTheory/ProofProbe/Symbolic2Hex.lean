/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDetTheory

open Matrix

theorem HexPolyDetTheory.ProofProbe.Symbolic2Hex.result (x : Int) : Matrix.det (!![x, 1; 1, x] : Matrix (Fin 2) (Fin 2) Int) = x^2-1 := by
  det

/-- info: 'HexPolyDetTheory.ProofProbe.Symbolic2Hex.result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexPolyDetTheory.ProofProbe.Symbolic2Hex.result
