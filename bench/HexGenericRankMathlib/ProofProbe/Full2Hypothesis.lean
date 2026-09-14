/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGenericRankMathlib
import Mathlib.Algebra.Field.ZMod

set_option trace.Hex.genericRank true

open Matrix

theorem result (x : ℚ) (hx : x ≠ 0) : (!![x, 2*x; 0, 1]).rank = 2 := by
  rank

#print axioms result
