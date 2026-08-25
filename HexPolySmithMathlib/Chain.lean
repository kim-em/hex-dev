/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolySmithMathlib.Basis

public section

/-! The canonical divisibility chain carried by the executable Smith form. -/

namespace HexPolySmithMathlib

universe u

open Hex Hex.PolyMatrix

noncomputable section

/-- The diagonal in `smithNormalForm` is the executable invariant-factor
vector transported to Mathlib polynomials. -/
theorem smithNormalForm_a {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) (i : Fin (snfRank A)) :
    (smithNormalForm A).a i =
      HexPolyMathlib.toPolynomial (invariantFactors A)[i] := by
  rw [smithNormalForm_a_snfData, invariantFactors_get_eq]

/-- The canonical Smith coefficients form a divisibility chain. -/
theorem smithNormalForm_chain {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) (i : Nat)
    (h : i + 1 < snfRank A) :
    (smithNormalForm A).a ⟨i, by omega⟩ ∣
      (smithNormalForm A).a ⟨i + 1, h⟩ := by
  rw [smithNormalForm_a_snfData, smithNormalForm_a_snfData]
  apply HexPolyMathlib.toPolynomial_dvd
  simpa using (snfData_isSNF A).chain i
    (by simpa [snfRank_eq A] using h)

end

end HexPolySmithMathlib
