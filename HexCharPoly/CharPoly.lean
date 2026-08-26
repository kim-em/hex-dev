/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexCharPoly.Berkowitz
public import HexPoly

public section

/-!
The normalized dense characteristic polynomial built from the descending
Samuelson--Berkowitz coefficient vector.
-/

namespace Hex.Matrix

universe u

variable {R : Type u} [Lean.Grind.CommRing R] [DecidableEq R] {n : Nat}

/-- The characteristic polynomial `det (x * I - A)`. -/
@[expose]
def charPoly (A : Matrix R n n) : DensePoly R :=
  DensePoly.ofCoeffs (berkowitz A).reverse.toArray

/-- Coefficient `k` of `charPoly` is entry `n-k` of the descending Berkowitz
vector. -/
@[simp, grind =]
theorem coeff_charPoly (A : Matrix R n n) {k : Nat} (hk : k <= n) :
    (charPoly A).coeff k = (berkowitz A)[n - k] := by
  rw [charPoly, DensePoly.coeff_ofCoeffs]
  have hkn : k < n + 1 := by omega
  change (berkowitz A).reverse.toArray.getD k (0 : R) = _
  rw [← Array.getElem_eq_getD (xs := (berkowitz A).reverse.toArray) (i := k)
    (h := by simpa using hkn) (fallback := (0 : R))]
  simp only [Vector.getElem_toArray, Vector.getElem_reverse]
  congr 1

/-- Over a nontrivial coefficient ring, `charPoly` stores exactly `n+1`
coefficients. -/
theorem size_charPoly (h1 : (1 : R) ≠ 0) (A : Matrix R n n) :
    (charPoly A).size = n + 1 := by
  have hle : (charPoly A).size <= n + 1 := by
    simpa [charPoly] using
      DensePoly.size_ofCoeffs_le (R := R) (berkowitz A).reverse.toArray
  have htop : (charPoly A).coeff n = 1 := by
    rw [coeff_charPoly A (Nat.le_refl n)]
    simpa using berkowitz_zero A
  have hlt : n < (charPoly A).size := by
    by_cases h : (charPoly A).size <= n
    · have hz := DensePoly.coeff_eq_zero_of_size_le (charPoly A) h
      rw [htop] at hz
      exact False.elim (h1 hz)
    · omega
  omega

/-- Over a nontrivial coefficient ring, `charPoly` has degree `n`. -/
theorem degree?_charPoly (h1 : (1 : R) ≠ 0) (A : Matrix R n n) :
    (charPoly A).degree? = some n := by
  rw [DensePoly.degree?_eq_some_of_pos_size (charPoly A) (by
    rw [size_charPoly h1 A]
    omega)]
  rw [size_charPoly h1 A]
  congr 1

/-- The characteristic polynomial is monic, including over the zero ring. -/
theorem charPoly_monic (A : Matrix R n n) : (charPoly A).Monic := by
  by_cases h1 : (1 : R) = 0
  · unfold DensePoly.Monic
    have hz : (charPoly A).leadingCoeff = 0 := by
      calc
        (charPoly A).leadingCoeff = (charPoly A).leadingCoeff * 1 :=
          (Lean.Grind.Semiring.mul_one _).symm
        _ = (charPoly A).leadingCoeff * 0 := by rw [h1]
        _ = 0 := Lean.Grind.Semiring.mul_zero _
    rw [hz, h1]
  · unfold DensePoly.Monic
    have hsize := size_charPoly h1 A
    rw [DensePoly.leadingCoeff_eq_coeff_last (charPoly A) (by omega), hsize]
    have hsub : n + 1 - 1 = n := by omega
    rw [hsub, coeff_charPoly A (Nat.le_refl n)]
    simpa using berkowitz_zero A

end Hex.Matrix
