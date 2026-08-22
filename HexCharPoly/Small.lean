/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexCharPoly.CharPoly

public section

/-!
Closed forms for characteristic polynomials in dimensions zero, one, and two.
-/

namespace Hex.Matrix

universe u

variable {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R]

/-- The characteristic polynomial of the empty matrix is one. -/
@[simp, grind =]
theorem charPoly_empty (A : Matrix R 0 0) : charPoly A = 1 := by
  rfl

/-- The characteristic polynomial of a one-by-one matrix is `x - A[0,0]`. -/
theorem charPoly_one_by_one (A : Matrix R 1 1) :
    charPoly A = DensePoly.ofCoeffs #[-A[(0, 0)], 1] := by
  have hberk : berkowitz A = #v[(1 : R), -A[(0, 0)]] := by
    apply Vector.ext
    intro i hi
    have hcases : i = 0 ∨ i = 1 := by omega
    rcases hcases with rfl | rfl <;>
      simp [berkowitz, berkowitzAux, berkowitzStep, toeplitzMulVec,
        berkowitzColumn, berkowitzRow, berkowitzCol, List.finRange_succ] <;>
      grind
  apply DensePoly.ext_coeff
  intro i
  by_cases hi : i <= 1
  · have hcases : i = 0 ∨ i = 1 := by omega
    rcases hcases with rfl | rfl <;>
      rw [coeff_charPoly A (by omega), hberk] <;> simp
  · have hsize : (charPoly A).size <= 2 := by
      simpa [charPoly] using
        DensePoly.size_ofCoeffs_le (R := R) (berkowitz A).reverse.toArray
    rw [DensePoly.coeff_eq_zero_of_size_le (charPoly A) (by omega),
      DensePoly.coeff_ofCoeffs]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp; omega)]
    rfl

/-- The usual closed form for the characteristic polynomial of a two-by-two
matrix. -/
theorem charPoly_two_by_two (A : Matrix R 2 2) :
    charPoly A = DensePoly.ofCoeffs
      #[A[(0, 0)] * A[(1, 1)] - A[(0, 1)] * A[(1, 0)],
        -(A[(0, 0)] + A[(1, 1)]), 1] := by
  have hberk : berkowitz A =
      #v[(1 : R), -(A[(0, 0)] + A[(1, 1)]),
        A[(0, 0)] * A[(1, 1)] - A[(0, 1)] * A[(1, 0)]] := by
    apply Vector.ext
    intro i hi
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hcases with rfl | rfl | rfl <;>
      simp [berkowitz, berkowitzAux, berkowitzStep, toeplitzMulVec,
        berkowitzColumn, berkowitzRow, berkowitzCol, berkowitzMoments,
        Vector.dotProduct,
        List.finRange_succ] <;>
      grind
  apply DensePoly.ext_coeff
  intro i
  by_cases hi : i <= 2
  · have hcases : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hcases with rfl | rfl | rfl <;>
      rw [coeff_charPoly A (by omega), hberk] <;> simp
  · have hsize : (charPoly A).size <= 3 := by
      simpa [charPoly] using
        DensePoly.size_ofCoeffs_le (R := R) (berkowitz A).reverse.toArray
    rw [DensePoly.coeff_eq_zero_of_size_le (charPoly A) (by omega),
      DensePoly.coeff_ofCoeffs]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by simp; omega)]
    rfl

end Hex.Matrix
