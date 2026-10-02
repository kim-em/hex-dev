/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDetMathlib

open Matrix

theorem HexPolyDetMathlib.Diagnostics.generic {R : Type} [CommRing R] (a b c d e f g h i j k l : R) : Matrix.det !![a, b, c, d; e, f, g, h; i, j, k, l; a+e, b+f, c+g, d+h] = 0 := by
  det

/-- info: 'HexPolyDetMathlib.Diagnostics.generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HexPolyDetMathlib.Diagnostics.generic
