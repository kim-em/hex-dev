/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Tactic

set_option maxHeartbeats 0
set_option profiler true

theorem result (x : Int) : (x + 1) ^ 4 = x ^ 4 + 4 * x ^ 3 + 6 * x ^ 2 + 4 * x + 1 := by
  grobner

#print axioms result
