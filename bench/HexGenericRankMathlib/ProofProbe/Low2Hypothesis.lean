/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGenericRankMathlib
import Mathlib.Algebra.Field.ZMod

set_option profiler true
set_option profiler.threshold 1000000
set_option trace.Hex.genericRank true

open Matrix

theorem result (x : ℚ) (hx : x ≠ 0) : (!![x, 2*x^2; 3*x, 6*x^2]).rank = 1 := by
  rank

#print axioms result
