/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultantMathlib.Sylvester

public section

/-!
Agreement of the executable discriminant with Mathlib.
-/
namespace Hex.DensePoly

universe u

variable {R : Type u}

/-- The executable and Mathlib discriminants agree under dense-polynomial
correspondence. -/
theorem toPolynomial_disc [CommRing R] [IsDomain R] [DecidableEq R]
    [Div R] [Hex.ExactDivLaws R] (f : DensePoly R) :
    disc f = Polynomial.discr (HexPolyMathlib.toPolynomial f) := by
  let F := HexPolyMathlib.toPolynomial f
  by_cases hsmall : f.size ≤ 1
  · unfold disc
    rw [if_pos hsmall]
    have hdeg : F.natDegree = 0 := by
      rw [show F.natDegree = f.degree?.getD 0 by
        simpa only [F] using HexPolyMathlib.natDegree_toPolynomial f]
      by_cases hf : f = 0
      · subst f
        simp
      · have hfpos : 0 < f.size := by
          by_contra h
          apply hf
          exact (size_eq_zero_iff f).mp (by omega)
        rw [degree?_eq_some_of_pos_size f hfpos, Option.getD_some]
        omega
    change 1 = Polynomial.discr F
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdeg]
    exact (Polynomial.discr_C _).symm
  · let n := f.size - 1
    let d := f.derivative
    let D := HexPolyMathlib.toPolynomial d
    let k := d.degree?.getD 0
    let gap := n - 1 - k
    have hfpos : 0 < f.size := by omega
    have hn : 0 < n := by
      dsimp only [n]
      omega
    have hFn : F.natDegree = n := by
      rw [show F.natDegree = f.degree?.getD 0 by
        simpa only [F] using HexPolyMathlib.natDegree_toPolynomial f]
      rw [degree?_eq_some_of_pos_size f hfpos, Option.getD_some]
    have hD : D = F.derivative := by
      simpa only [D, d, F] using HexPolyMathlib.toPolynomial_derivative f
    have hDk : D.natDegree = k := by
      simpa only [D, k] using HexPolyMathlib.natDegree_toPolynomial d
    have hk : k ≤ n - 1 := by
      rw [← hDk, hD, ← hFn]
      exact Polynomial.natDegree_derivative_le F
    have hkgap : k + gap = n - 1 := by
      dsimp only [gap]
      omega
    have hlc : F.leadingCoeff = f.leadingCoeff := by
      simpa only [F] using HexPolyMathlib.leadingCoeff_toPolynomial f
    have hactual :
        resultant f d = Polynomial.resultant F D n k := by
      rw [toPolynomial_resultant]
      rw [show f.degree?.getD 0 = n by
        rw [degree?_eq_some_of_pos_size f hfpos, Option.getD_some]]
    have hpromote :
        powNat f.leadingCoeff gap * resultant f d =
          Polynomial.resultant F F.derivative n (n - 1) := by
      have hadd := Polynomial.resultant_add_right_deg F D n k gap
        (by rw [hDk])
      rw [hkgap, hD] at hadd
      have hcoeff : F.coeff n = F.leadingCoeff := by
        rw [← hFn]
        exact Polynomial.coeff_natDegree
      rw [powNat_eq_pow, hactual, ← hlc, hD, ← hcoeff]
      exact hadd.symm
    have hdegree : 0 < F.degree := by
      rw [← Polynomial.natDegree_pos_iff_degree_pos, hFn]
      exact hn
    have hformal := Polynomial.resultant_deriv (f := F) hdegree
    rw [hFn] at hformal
    rw [hlc] at hformal
    unfold disc
    rw [if_neg hsmall]
    change
      negOnePow (R := R) (n * (n - 1) / 2) *
          exactDiv (powNat f.leadingCoeff gap * resultant f d)
            f.leadingCoeff =
        Polynomial.discr F
    rw [show powNat f.leadingCoeff (n - 1 - k) * resultant f d =
        Polynomial.resultant F F.derivative n (n - 1) by
      simpa only [gap] using hpromote]
    rw [hformal]
    rw [negOnePow_eq_sign,
      Hex.SubresultantMinor.sign_eq_pow]
    have hflc : f.leadingCoeff ≠ 0 :=
      leadingCoeff_ne_zero_of_pos_size f hfpos
    have hdiv :
        exactDiv
            ((-1 : R) ^ (n * (n - 1) / 2) * f.leadingCoeff *
              Polynomial.discr F)
            f.leadingCoeff =
          (-1 : R) ^ (n * (n - 1) / 2) * Polynomial.discr F := by
      rw [show
          (-1 : R) ^ (n * (n - 1) / 2) * f.leadingCoeff *
              Polynomial.discr F =
            ((-1 : R) ^ (n * (n - 1) / 2) * Polynomial.discr F) *
              f.leadingCoeff by ring]
      exact Hex.exactDiv_mul_right _ hflc
    rw [hdiv]
    have hsign :
        (-1 : R) ^ (n * (n - 1) / 2) *
            (-1 : R) ^ (n * (n - 1) / 2) = 1 := by
      simpa only [← Hex.SubresultantMinor.sign_eq_pow] using
        (Hex.SubresultantMinor.sign_mul_self (R := R)
          (n * (n - 1) / 2))
    rw [← mul_assoc, hsign, one_mul]

end Hex.DensePoly
