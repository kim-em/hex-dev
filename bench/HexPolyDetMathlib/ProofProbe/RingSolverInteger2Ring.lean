/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Tactic

set_option maxHeartbeats 0
set_option profiler true

theorem result (x y : Int) : (x + 1) * (x - 1) - y * y = x ^ 2 - y ^ 2 - 1 := by
  ring

#print axioms result
