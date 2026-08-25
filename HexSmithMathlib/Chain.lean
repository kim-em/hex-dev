/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module


public import HexSmithMathlib.Basis

public section

/-! The canonical divisibility chain omitted by Mathlib's Smith structure. -/

namespace HexSmithMathlib

/-- Consecutive coefficients of the executable Mathlib Smith basis form a
divisibility chain. -/
theorem smithNormalForm_chain (A : Hex.Matrix Int n m) (i : Nat)
    (h : i + 1 < Hex.Matrix.snfRank A) :
    (smithNormalForm A).a ⟨i, by omega⟩ ∣
      (smithNormalForm A).a ⟨i + 1, h⟩ := by
  rw [smithNormalForm_a, smithNormalForm_a]
  exact Hex.Matrix.invariantFactors_chain A i h

end HexSmithMathlib
