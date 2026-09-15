/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Tactic

set_option maxHeartbeats 0
set_option profiler true

theorem result (x : Int) : x ^ 4 * x ^ 3 * x ^ 2 - x ^ 4 * 1 * 1 - 1 * 1 * x ^ 2 + 1 * 1 * 0 + 0 * 1 * 1 - 0 * x ^ 3 * 0 = x ^ 9 - x ^ 4 - x ^ 2 := by
  ring

#print axioms result
