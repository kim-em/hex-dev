/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldTowerMathlib.NormCore.Basic
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

public section

namespace Hex.NumberTower.Norm

open Polynomial

/-- The quadratic norm identity, with formal degrees so the linear
coefficient may vanish. -/
theorem quadratic_resultant (a b p q : ℂ) :
    resultant (X ^ 2 + C b * X + C a) (C p + C q * X) 2 1 =
      p * p - b * p * q + a * q * q := by
  simp [resultant, Matrix.det_fin_three, sylvester, Matrix.of_apply,
    Fin.addCases, Set.mem_Icc, coeff_X]
  ring_nf
  simp

/-- Replacing a polynomial by a linear expression with the same values on
the roots of a monic quadratic preserves its resultant, including repeated
roots and a vanishing linear coefficient. -/
theorem quadratic_congr (a b p q : ℂ) (g : Polynomial ℂ) (n : Nat)
    (hn : g.natDegree ≤ n)
    (heval : ∀ z : ℂ, z * z + b * z + a = 0 → g.eval z = p + q * z) :
    resultant (X ^ 2 + C b * X + C a) g 2 n =
      p * p - b * p * q + a * q * q := by
  let f : Polynomial ℂ := X ^ 2 + C b * X + C a
  let h : Polynomial ℂ := C p + C q * X
  have hf : IsMonicOfDegree f 2 := isMonicOfDegree_add_add_two b a
  have hh : h.natDegree ≤ 1 := by
    simpa [h, add_comm] using (natDegree_linear_le (a := q) (b := p))
  have hprod : (f.roots.map g.eval).prod = (f.roots.map h.eval).prod := by
    congr 1
    apply Multiset.map_congr rfl
    intro z hz
    have hz' := (mem_roots hf.monic.ne_zero).mp hz
    have hroot : z * z + b * z + a = 0 := by
      simpa [f, IsRoot, pow_two] using hz'
    simpa [h] using heval z hroot
  calc
    resultant f g 2 n = (f.roots.map g.eval).prod := by
      simpa [hf.natDegree_eq, hf.leadingCoeff_eq] using
        resultant_eq_prod_eval f g n hn (IsAlgClosed.splits f)
    _ = (f.roots.map h.eval).prod := hprod
    _ = resultant f h 2 1 := by
      symm
      simpa [hf.natDegree_eq, hf.leadingCoeff_eq] using
        resultant_eq_prod_eval f h 1 hh (IsAlgClosed.splits f)
    _ = p * p - b * p * q + a * q * q := quadratic_resultant a b p q

noncomputable section

variable {R : Type*} [CommRing R] [DecidableEq R]

local instance : CommRing (DensePoly R) := denseCommRing

private theorem poly_pair (a b : R) :
    HexPolyMathlib.toPolynomial (DensePoly.ofCoeffs #[a, b]) = C a + X * C b := by
  simp [Finset.sum_range_succ, Array.getD]

private theorem poly_three (a b : R) :
    HexPolyMathlib.toPolynomial (DensePoly.ofCoeffs #[a, b, 1]) =
      X ^ 2 + C b * X + C a := by
  simp [Finset.sum_range_succ, Array.getD]
  ring

private theorem map_scale (φ : DensePoly R →+* ℂ) (k : R) (p : DensePoly R) :
    φ (DensePoly.scale k p) = φ (DensePoly.C k) * φ p := by
  have heq : DensePoly.scale k p = DensePoly.C k * p := by
    apply (HexPolyMathlib.equiv (R := R)).injective
    simp
  rw [heq, map_mul]

private theorem map_shift (φ : DensePoly R →+* ℂ) (p : DensePoly R) :
    φ (DensePoly.shift 1 p) = φ (DensePoly.monomial 1 1) * φ p := by
  have heq : DensePoly.shift 1 p = DensePoly.monomial 1 1 * p := by
    apply (HexPolyMathlib.equiv (R := R)).injective
    change HexPolyMathlib.toPolynomial (DensePoly.shift 1 p) =
      HexPolyMathlib.toPolynomial (DensePoly.monomial 1 1 * p)
    rw [HexPolyMathlib.toPolynomial_mul, HexPolyMathlib.toPolynomial_monomial,
      monomial_one_one_eq_X]
    ext n
    cases n <;> simp [HexPolyMathlib.coeff_toPolynomial]
    rfl
  rw [heq, map_mul]

end

end Hex.NumberTower.Norm
