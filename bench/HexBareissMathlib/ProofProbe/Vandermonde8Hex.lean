/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexBareissMathlib

/-! `Vandermonde8Hex`: the `vandermonde-8` family, a `8 × 8` literal over `ℤ`, proved by `det`. -/

set_option maxHeartbeats 0

theorem result : Matrix.det (R := ℤ) !![0, 0, 0, 0, 0, 0, 0, 1; 1, 1, 1, 1, 1, 1, 1, 1; 128, 64, 32, 16, 8, 4, 2, 1; 2187, 729, 243, 81, 27, 9, 3, 1; 16384, 4096, 1024, 256, 64, 16, 4, 1; 78125, 15625, 3125, 625, 125, 25, 5, 1; 279936, 46656, 7776, 1296, 216, 36, 6, 1; 823543, 117649, 16807, 2401, 343, 49, 7, 1] = 125411328000 := by det

#print axioms result
