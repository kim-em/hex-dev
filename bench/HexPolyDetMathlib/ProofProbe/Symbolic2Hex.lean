/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyDetMathlib

public section

open Matrix

theorem HexPolyDetMathlib.ProofProbe.Symbolic2Hex.result (x : Int) : Matrix.det (!![x, 1; 1, x] : Matrix (Fin 2) (Fin 2) Int) = x^2-1 := by
  det

/-- info: 'HexPolyDetMathlib.ProofProbe.Symbolic2Hex.result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexPolyDetMathlib.ProofProbe.Symbolic2Hex.result
