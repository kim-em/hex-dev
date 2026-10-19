/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDetTheory

open Matrix

def HexPolyDetTheory.Diagnostics.symbolicResult (x : Int) : {d : Int // Matrix.det (!![x, 1, 0; 1, x, 1; 0, 1, x] : Matrix (Fin 3) (Fin 3) Int) = d} := by
  let c := det% (!![x, 1, 0; 1, x, 1; 0, 1, x] : Matrix (Fin 3) (Fin 3) Int)
  exact ⟨c.value, c.proof⟩

/-- info: 'HexPolyDetTheory.Diagnostics.symbolicResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexPolyDetTheory.Diagnostics.symbolicResult
