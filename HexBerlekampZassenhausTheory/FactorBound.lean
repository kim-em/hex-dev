/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus
public import HexPolyZTheory.Mignotte

public section
set_option backward.proofsInPublic true

/-!
# Factor coefficient bounds

Degree, norm, coefficient, and leading-coefficient bounds for integer
polynomial factors.
-/

namespace HexBerlekampZassenhausTheory

noncomputable section

open Polynomial

/--
The transported degree of an executable divisor is bounded by the executable
degree of the ambient nonzero polynomial.
-/
theorem natDegree_toPolynomial_le_degree_getD_of_dvd
    (f g : Hex.ZPoly) (hf : f ≠ 0) (hgf : g ∣ f) :
    (HexPolyZTheory.toPolynomial g).natDegree ≤ f.natDegree := by
  have hf_poly : HexPolyZTheory.toPolynomial f ≠ 0 := by
    intro h
    apply hf
    apply HexPolyZTheory.equiv.injective
    simpa using h
  have hgf_poly :
      HexPolyZTheory.toPolynomial g ∣ HexPolyZTheory.toPolynomial f :=
    HexPolyTheory.toPolynomial_dvd hgf
  have hbound :=
    Polynomial.natDegree_le_of_dvd hgf_poly hf_poly
  rw [HexPolyTheory.natDegree_toPolynomial f] at hbound
  exact hbound

/--
The executable natural L2 bound dominates the real coefficient-vector norm used
by the Mathlib Mignotte theorem.
-/
theorem l2norm_toPolynomial_le_coeffL2NormBound (f : Hex.ZPoly) :
    HexPolyZTheory.l2norm (HexPolyZTheory.toPolynomial f) ≤
      (Hex.ZPoly.coeffL2NormBound f : ℝ) := by
  have hsq :=
    HexPolyZTheory.l2norm_toPolynomial_sq_le_coeffNormSq f
  have hceil_nat :
      Hex.ZPoly.coeffNormSq f ≤ (Hex.ZPoly.coeffL2NormBound f) ^ 2 := by
    simpa [Hex.ZPoly.coeffL2NormBound_eq_ceilSqrt_coeffNormSq] using
      Hex.ZPoly.le_ceilSqrt_sq (Hex.ZPoly.coeffNormSq f)
  have hceil_real :
      (Hex.ZPoly.coeffNormSq f : ℝ) ≤
        (Hex.ZPoly.coeffL2NormBound f : ℝ) ^ 2 := by
    exact_mod_cast hceil_nat
  exact le_of_sq_le_sq (hsq.trans hceil_real) (by positivity)

/--
The default executable factorization bound is strong enough for every
coefficient of every executable divisor of a nonzero input.
-/
theorem defaultFactorCoeffBound_valid
    (f : Hex.ZPoly) (hf : f ≠ 0) :
    ∀ g : Hex.ZPoly, g ∣ f → ∀ i, (g.coeff i).natAbs ≤ Hex.ZPoly.defaultFactorCoeffBound f := by
  intro g hgf i
  have hf_poly : HexPolyZTheory.toPolynomial f ≠ 0 := by
    intro h
    apply hf
    exact HexPolyZTheory.equiv.injective (by simpa using h)
  have hgf_poly : HexPolyZTheory.toPolynomial g ∣ HexPolyZTheory.toPolynomial f :=
    HexPolyTheory.toPolynomial_dvd hgf
  have hdegree :
      (HexPolyZTheory.toPolynomial g).natDegree ≤ f.natDegree :=
    natDegree_toPolynomial_le_degree_getD_of_dvd f g hf hgf
  have hcoeff_eq : (HexPolyZTheory.toPolynomial g).coeff i = g.coeff i :=
    HexPolyZTheory.coeff_toPolynomial g i
  by_cases hi : i ≤ (HexPolyZTheory.toPolynomial g).natDegree
  · -- The interesting case: i is within the factor's natural degree.
    have hmignotte :=
      HexPolyZTheory.mignotte_bound
        (HexPolyZTheory.toPolynomial f) (HexPolyZTheory.toPolynomial g)
        hf_poly hgf_poly i
    rw [hcoeff_eq] at hmignotte
    have hl2 :
        HexPolyZTheory.l2norm (HexPolyZTheory.toPolynomial f) ≤
          (Hex.ZPoly.coeffL2NormBound f : ℝ) :=
      l2norm_toPolynomial_le_coeffL2NormBound f
    have hchoose_nonneg :
        (0 : ℝ) ≤ Nat.choose (HexPolyZTheory.toPolynomial g).natDegree i :=
      Nat.cast_nonneg _
    have hstep :
        ((g.coeff i).natAbs : ℝ) ≤
          (Nat.choose (HexPolyZTheory.toPolynomial g).natDegree i : ℝ) *
            (Hex.ZPoly.coeffL2NormBound f : ℝ) :=
      hmignotte.trans (mul_le_mul_of_nonneg_left hl2 hchoose_nonneg)
    have hbinom :
        (Nat.choose (HexPolyZTheory.toPolynomial g).natDegree i : ℝ) =
          (Hex.Nat.binom (HexPolyZTheory.toPolynomial g).natDegree i : ℝ) := by
      rw [HexPolyZTheory.binom_eq_choose]
    rw [hbinom] at hstep
    have huniform_nat :=
      Hex.ZPoly.mignotteCoeffBound_le_defaultFactorCoeffBound
        f (k := (HexPolyZTheory.toPolynomial g).natDegree) (j := i) hdegree hi
    have hmig_eq :
        Hex.ZPoly.mignotteCoeffBound f
            (HexPolyZTheory.toPolynomial g).natDegree i =
          Hex.Nat.binom (HexPolyZTheory.toPolynomial g).natDegree i *
            Hex.ZPoly.coeffL2NormBound f :=
      Hex.ZPoly.mignotteCoeffBound_eq f _ _
    have huniform_real :
        (Hex.Nat.binom (HexPolyZTheory.toPolynomial g).natDegree i : ℝ) *
          (Hex.ZPoly.coeffL2NormBound f : ℝ) ≤
          (Hex.ZPoly.defaultFactorCoeffBound f : ℝ) := by
      have := huniform_nat
      rw [hmig_eq] at this
      exact_mod_cast this
    have hfinal :
        ((g.coeff i).natAbs : ℝ) ≤ (Hex.ZPoly.defaultFactorCoeffBound f : ℝ) :=
      hstep.trans huniform_real
    exact_mod_cast hfinal
  · -- Outside the factor's natural degree the coefficient is zero.
    have hi' : (HexPolyZTheory.toPolynomial g).natDegree < i := Nat.lt_of_not_le hi
    have hcoeff_zero : (HexPolyZTheory.toPolynomial g).coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt hi'
    have hgcoeff_zero : g.coeff i = 0 := hcoeff_eq ▸ hcoeff_zero
    simp [hgcoeff_zero]

/--
The default recovery window also bounds the proportional factor reconstructed
by the direct-coordinate Hensel path.

When `factor * cofactor = core`, direct recombination reconstructs
`leadingCoeff cofactor • factor`.  The sharpened Mignotte inequality bounds
this polynomial by the same executable window as an ordinary divisor; no
leading-coefficient multiplier or squared bound is needed.
-/
theorem cofactorCoeff_le_defaultBound
    (core factor cofactor : Hex.ZPoly)
    (hcore_ne : core ≠ 0)
    (hproduct : factor * cofactor = core) :
    ∀ i,
      ((Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff cofactor) factor).coeff i).natAbs ≤
        Hex.ZPoly.defaultFactorCoeffBound core := by
  intro i
  have hfactor_dvd : factor ∣ core := ⟨cofactor, hproduct.symm⟩
  have hdegree :
      (HexPolyZTheory.toPolynomial factor).natDegree ≤ core.natDegree :=
    natDegree_toPolynomial_le_degree_getD_of_dvd
      core factor hcore_ne hfactor_dvd
  have hpoly_product :
      HexPolyZTheory.toPolynomial factor *
          HexPolyZTheory.toPolynomial cofactor =
        HexPolyZTheory.toPolynomial core := by
    rw [← HexPolyZTheory.toPolynomial_mul, hproduct]
  have hmignotte :=
    HexPolyZTheory.mignotte_cofactor_bound
      (HexPolyZTheory.toPolynomial factor)
      (HexPolyZTheory.toPolynomial cofactor) i
  rw [hpoly_product, HexPolyTheory.leadingCoeff_toPolynomial,
    HexPolyZTheory.coeff_toPolynomial] at hmignotte
  have hscaled_coeff :
      (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff cofactor) factor).coeff i =
        Hex.DensePoly.leadingCoeff cofactor * factor.coeff i := by
    rw [Hex.DensePoly.coeff_scale (R := Int)
      (Hex.DensePoly.leadingCoeff cofactor) factor i (Int.mul_zero _)]
  rw [hscaled_coeff]
  by_cases hi : i ≤ (HexPolyZTheory.toPolynomial factor).natDegree
  · have hl2 :
        HexPolyZTheory.l2norm (HexPolyZTheory.toPolynomial core) ≤
          (Hex.ZPoly.coeffL2NormBound core : ℝ) :=
      l2norm_toPolynomial_le_coeffL2NormBound core
    have hchoose_nonneg :
        (0 : ℝ) ≤ Nat.choose (HexPolyZTheory.toPolynomial factor).natDegree i :=
      Nat.cast_nonneg _
    have hstep :
        ((Hex.DensePoly.leadingCoeff cofactor * factor.coeff i).natAbs : ℝ) ≤
          (Nat.choose (HexPolyZTheory.toPolynomial factor).natDegree i : ℝ) *
            (Hex.ZPoly.coeffL2NormBound core : ℝ) :=
      hmignotte.trans (mul_le_mul_of_nonneg_left hl2 hchoose_nonneg)
    have hbinom :
        (Nat.choose (HexPolyZTheory.toPolynomial factor).natDegree i : ℝ) =
          (Hex.Nat.binom (HexPolyZTheory.toPolynomial factor).natDegree i : ℝ) := by
      rw [HexPolyZTheory.binom_eq_choose]
    rw [hbinom] at hstep
    have huniform_nat :=
      Hex.ZPoly.mignotteCoeffBound_le_defaultFactorCoeffBound
        core (k := (HexPolyZTheory.toPolynomial factor).natDegree) (j := i)
        hdegree hi
    have hmig_eq :
        Hex.ZPoly.mignotteCoeffBound core
            (HexPolyZTheory.toPolynomial factor).natDegree i =
          Hex.Nat.binom (HexPolyZTheory.toPolynomial factor).natDegree i *
            Hex.ZPoly.coeffL2NormBound core :=
      Hex.ZPoly.mignotteCoeffBound_eq core _ _
    have huniform_real :
        (Hex.Nat.binom (HexPolyZTheory.toPolynomial factor).natDegree i : ℝ) *
            (Hex.ZPoly.coeffL2NormBound core : ℝ) ≤
          (Hex.ZPoly.defaultFactorCoeffBound core : ℝ) := by
      rw [hmig_eq] at huniform_nat
      exact_mod_cast huniform_nat
    exact_mod_cast hstep.trans huniform_real
  · have hi' : (HexPolyZTheory.toPolynomial factor).natDegree < i :=
      Nat.lt_of_not_le hi
    have hcoeff_zero :
        (HexPolyZTheory.toPolynomial factor).coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt hi'
    rw [HexPolyZTheory.coeff_toPolynomial] at hcoeff_zero
    simp [hcoeff_zero]

/-- The default factor coefficient bound dominates the natural absolute value
of the leading coefficient of any nonzero executable polynomial. Standard
packaging of `defaultFactorCoeffBound_valid` at
`g := f, hgf := f ∣ f, i := f.size - 1` paired with
`leadingCoeff_eq_coeff_last`. -/
theorem defaultFactorCoeffBound_leadingCoeff_natAbs_le
    {f : Hex.ZPoly} (hf : f ≠ 0) :
    (Hex.DensePoly.leadingCoeff f).natAbs ≤
      Hex.ZPoly.defaultFactorCoeffBound f := by
  have hsize_pos : 0 < f.size := Hex.ZPoly.size_pos_of_ne_zero _ hf
  have hf_dvd_self : f ∣ f :=
    ⟨(1 : Hex.ZPoly), (Hex.DensePoly.mul_one_right_poly f).symm⟩
  rw [Hex.DensePoly.leadingCoeff_eq_coeff_last f hsize_pos]
  exact defaultFactorCoeffBound_valid f hf f hf_dvd_self (f.size - 1)
/-- A polynomial with positive leading coefficient is nonzero. -/
theorem zpoly_ne_zero_of_pos_lc {f : Hex.ZPoly}
    (hpos : 0 < Hex.DensePoly.leadingCoeff f) : f ≠ 0 := by
  intro hf
  rw [hf] at hpos
  have hzero_lc : Hex.DensePoly.leadingCoeff (0 : Hex.ZPoly) = 0 := rfl
  rw [hzero_lc] at hpos
  omega


end

end HexBerlekampZassenhausTheory
