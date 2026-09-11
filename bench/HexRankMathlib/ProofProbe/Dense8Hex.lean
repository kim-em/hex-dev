/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRankMathlib

/-! `Dense8`: a `8 × 8` integer literal of rank `8`, proved by `rank`. -/

set_option maxHeartbeats 0

theorem result : Matrix.rank (R := ℤ) !![1, -9, -3, 0, -8, -3, 4, 7; 9, -7, 0, -7, 8, -5, 3, -9; -6, 1, -2, 1, -6, -1, 0, -1; -8, -4, 8, -6, -6, 5, 5, -4; -1, -1, -4, -9, 2, -6, 0, 8; 1, 6, -6, 2, 2, 1, 2, 8; -8, 5, -8, 3, 8, 2, 8, -8; -7, -7, -5, -5, 7, 0, -5, 9] = 8 := by rank

#print axioms result
