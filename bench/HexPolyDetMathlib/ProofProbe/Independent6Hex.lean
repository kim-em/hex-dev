/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyDetMathlib

open Matrix

private theorem result (a b c d e f g h i j k l u v w x y z : Rat) : Matrix.det !![a/u, b/v, c/w, d/x, e/y, f/z; g/u, h/v, i/w, j/x, k/y, l/z; 1, 0, 0, 0, 0, 0; 0, 1, 0, 0, 0, 0; 0, 0, 1, 0, 0, 0; (a/u)+(g/u), (b/v)+(h/v), (c/w)+(i/w), (d/x)+(j/x), (e/y)+(k/y), (f/z)+(l/z)] = 0 := by
  det

#print axioms result
