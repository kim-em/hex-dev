/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Tactic.NormDet
import Mathlib.Tactic.Ring

open Matrix

private theorem result (a b c d u v w z : Rat) : Matrix.det !![a*c/(u*w), a*d/(u*z), 0, 0, 0; b*c/(v*w), b*d/(v*z), 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1] = 0 := by
  simp only [norm_det] <;> ring

#print axioms result
