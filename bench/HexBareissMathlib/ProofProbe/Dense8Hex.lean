/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexBareissMathlib

/-! `Dense8Hex`: the `dense-8` family, a `8 × 8` literal over `ℤ`, proved by `det`. -/

set_option maxHeartbeats 0

theorem result : Matrix.det (R := ℤ) !![104, -2, 81, 33, -95, -124, 40, -75; -6, 23, 60, 82, -63, -102, -107, -124; 88, -126, -37, 81, 56, 22, 103, -42; 104, 77, 62, -70, -23, 37, 92, 50; -52, -57, -30, -35, 96, -25, 63, -119; 37, 62, 45, -36, -16, 120, -13, -22; -122, -73, -103, 126, -32, -28, -76, 76; 111, -63, 118, -104, 7, 96, -22, -104] = 25666236444093325 := by det

#print axioms result
