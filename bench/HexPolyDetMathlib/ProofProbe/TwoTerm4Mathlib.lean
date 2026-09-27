/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import Mathlib.Tactic.NormDet
import Mathlib.Tactic.Ring

open Matrix

private theorem result (a b u : Rat) : Matrix.det !![(a+b)/u, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] = (a+b)/u := by
  simp only [norm_det] <;> ring

#print axioms result
