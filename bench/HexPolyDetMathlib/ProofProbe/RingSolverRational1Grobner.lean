/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Tactic

set_option maxHeartbeats 0
set_option profiler true

theorem result (x : Rat) : x / 2 + x / 3 = 5 * x / 6 := by
  grobner

#print axioms result
