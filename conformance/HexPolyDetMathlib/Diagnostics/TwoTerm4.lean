/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyDetMathlib

public section

open Matrix

theorem HexPolyDetMathlib.Diagnostics.twoTerm (a b u : Rat) : Matrix.det !![(a+b)/u, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] = (a+b)/u := by
  det

/-- info: 'HexPolyDetMathlib.Diagnostics.twoTerm' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexPolyDetMathlib.Diagnostics.twoTerm
