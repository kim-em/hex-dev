/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGenericRankMathlib
import Mathlib.Algebra.Field.ZMod

set_option maxHeartbeats 0
set_option profiler true
set_option profiler.threshold 1000000
set_option trace.Hex.genericRank true

open Matrix

theorem result (x : ℚ) (h : True → x ^ 2 - 1 ≠ 0) : (!![x, 1; 1, x]).rank = 2 := by
  rank
  guard_target = x ^ 2 - 1 ≠ 0
  exact h trivial

#print axioms result
