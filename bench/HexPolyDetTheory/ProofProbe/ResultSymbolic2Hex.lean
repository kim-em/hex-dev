/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDetTheory

open Matrix

def HexPolyDetTheory.ProofProbe.ResultSymbolic2Hex.certificate (x : Int) : {d : Int // Matrix.det (!![x, 1; 1, x] : Matrix (Fin 2) (Fin 2) Int) = d} := by
  let c := det% (!![x, 1; 1, x] : Matrix (Fin 2) (Fin 2) Int)
  exact ⟨c.value, c.proof⟩

/-- info: 'HexPolyDetTheory.ProofProbe.ResultSymbolic2Hex.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexPolyDetTheory.ProofProbe.ResultSymbolic2Hex.certificate
