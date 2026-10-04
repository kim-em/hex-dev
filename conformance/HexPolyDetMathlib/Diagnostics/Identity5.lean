/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyDetMathlib

public section

open Matrix

theorem HexPolyDetMathlib.Diagnostics.identity (x : Int) : Matrix.det !![1 + 1*x, 2*x, 3*x, 4*x, 5*x; 2*x, 1 + 4*x, 6*x, 8*x, 10*x; 3*x, 6*x, 1 + 9*x, 12*x, 15*x; 4*x, 8*x, 12*x, 1 + 16*x, 20*x; 5*x, 10*x, 15*x, 20*x, 1 + 25*x] = 1+55*x := by
  det

/-- info: 'HexPolyDetMathlib.Diagnostics.identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexPolyDetMathlib.Diagnostics.identity
