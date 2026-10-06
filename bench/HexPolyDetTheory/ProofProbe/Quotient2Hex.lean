/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDetTheory

open Matrix

theorem HexPolyDetTheory.ProofProbe.Quotient2Hex.result (a b c d u v w x : Rat) : Matrix.det (!![a/u, b/v; c/w, d/x] : Matrix (Fin 2) (Fin 2) Rat) = a*d/(u*x)-b*c/(v*w) := by
  det

/-- info: 'HexPolyDetTheory.ProofProbe.Quotient2Hex.result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexPolyDetTheory.ProofProbe.Quotient2Hex.result
