/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDetTheory

open Matrix

def HexPolyDetTheory.Diagnostics.identityResult (x : Int) : {d : Int // Matrix.det !![1 + 1*x, 2*x, 3*x, 4*x; 2*x, 1 + 4*x, 6*x, 8*x; 3*x, 6*x, 1 + 9*x, 12*x; 4*x, 8*x, 12*x, 1 + 16*x] = d} := by
  let c := det% !![1 + 1*x, 2*x, 3*x, 4*x; 2*x, 1 + 4*x, 6*x, 8*x; 3*x, 6*x, 1 + 9*x, 12*x; 4*x, 8*x, 12*x, 1 + 16*x]
  exact ⟨c.value, c.proof⟩

/-- info: 'HexPolyDetTheory.Diagnostics.identityResult' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexPolyDetTheory.Diagnostics.identityResult
