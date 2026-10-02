/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDetMathlib

open Matrix

theorem HexPolyDetMathlib.Diagnostics.degreeEight (a b u : Rat) : Matrix.det !![(a+b)^8/u, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] = (a+b)^8/u := by
  det

/-- info: 'HexPolyDetMathlib.Diagnostics.degreeEight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexPolyDetMathlib.Diagnostics.degreeEight
