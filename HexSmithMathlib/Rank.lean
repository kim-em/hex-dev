/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexSmith
public import HexHermiteMathlib.Rank

public section

/-! The executable Smith rank agrees with Mathlib's integer matrix rank. -/

namespace HexSmithMathlib

open HexMatrixMathlib

/-- The executable Smith rank is Mathlib's rank of the corresponding matrix. -/
theorem snfRank_eq_rank (A : Hex.Matrix Int n m) :
    Hex.Matrix.snfRank A = (matrixEquiv A).rank := by
  rw [Hex.Matrix.snfRank_eq_hnfRank, HexHermiteMathlib.hnfRank_eq_rank]

end HexSmithMathlib
