/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyZGcd.Maximal
public import HexPolyZMathlib.PolynomialEquivalence

public section

/-!
Transport of the checked integer-polynomial gcd API to Mathlib's
`Polynomial ℤ` representation.
-/

namespace HexPolyZGcdMathlib

open Hex

noncomputable section

/-- The transported checked gcd divides the left input. -/
theorem gcd_dvd_left (f h : ZPoly) :
    HexPolyZMathlib.equiv (ZPoly.gcd f h) ∣ HexPolyZMathlib.equiv f := by
  simpa only [HexPolyZMathlib.equiv_apply] using
    HexPolyMathlib.toPolynomial_dvd (ZPoly.gcd_dvd_left f h)

/-- The transported checked gcd divides the right input. -/
theorem gcd_dvd_right (f h : ZPoly) :
    HexPolyZMathlib.equiv (ZPoly.gcd f h) ∣ HexPolyZMathlib.equiv h := by
  simpa only [HexPolyZMathlib.equiv_apply] using
    HexPolyMathlib.toPolynomial_dvd (ZPoly.gcd_dvd_right f h)

/-- Every common executable divisor divides the transported checked gcd. -/
theorem dvd_gcd (d f h : ZPoly)
    (hdf : HexPolyZMathlib.equiv d ∣ HexPolyZMathlib.equiv f)
    (hdh : HexPolyZMathlib.equiv d ∣ HexPolyZMathlib.equiv h) :
    HexPolyZMathlib.equiv d ∣ HexPolyZMathlib.equiv (ZPoly.gcd f h) := by
  have hdf' : d ∣ f := by
    exact HexPolyMathlib.toPolynomial_dvd_iff.mp (by
      simpa only [HexPolyZMathlib.equiv_apply] using hdf)
  have hdh' : d ∣ h := by
    exact HexPolyMathlib.toPolynomial_dvd_iff.mp (by
      simpa only [HexPolyZMathlib.equiv_apply] using hdh)
  simpa only [HexPolyZMathlib.equiv_apply] using
    HexPolyMathlib.toPolynomial_dvd (ZPoly.dvd_gcd d f h hdf' hdh')

/-- Checked coprime cofactors establish greatestness after transport to
Mathlib polynomials. -/
theorem coprimeCofactors_greatest {f h g : ZPoly}
    (hc : ZPoly.CoprimeCofactors f h g) (d : ZPoly)
    (hdf : HexPolyZMathlib.equiv d ∣ HexPolyZMathlib.equiv f)
    (hdh : HexPolyZMathlib.equiv d ∣ HexPolyZMathlib.equiv h) :
    HexPolyZMathlib.equiv d ∣ HexPolyZMathlib.equiv g := by
  have hdf' : d ∣ f := HexPolyMathlib.toPolynomial_dvd_iff.mp (by
    simpa only [HexPolyZMathlib.equiv_apply] using hdf)
  have hdh' : d ∣ h := HexPolyMathlib.toPolynomial_dvd_iff.mp (by
    simpa only [HexPolyZMathlib.equiv_apply] using hdh)
  simpa only [HexPolyZMathlib.equiv_apply] using
    HexPolyMathlib.toPolynomial_dvd
      (ZPoly.dvd_gcd_of_coprimeCofactors hc d hdf' hdh')

/-- Checked exact division succeeds precisely for a nonzero divisor that
divides after transport to Mathlib polynomials. -/
theorem divExact?_eq_dvd (f g : ZPoly) :
    (ZPoly.divExact? f g).isSome = true ↔
      g ≠ 0 ∧ HexPolyZMathlib.equiv g ∣ HexPolyZMathlib.equiv f := by
  constructor
  · intro hsome
    cases hq : ZPoly.divExact? f g with
    | none => simp [hq] at hsome
    | some q =>
        refine ⟨?_, ?_⟩
        · intro hg
          subst g
          rw [ZPoly.divExact?_zero_right] at hq
          contradiction
        · apply HexPolyMathlib.toPolynomial_dvd
          refine ⟨q, ?_⟩
          rw [DensePoly.mul_comm_poly]
          exact (ZPoly.divExact?_product hq).symm
  · rintro ⟨hg, hdvd⟩
    have hdvd' : g ∣ f := HexPolyMathlib.toPolynomial_dvd_iff.mp (by
      simpa only [HexPolyZMathlib.equiv_apply] using hdvd)
    exact ZPoly.divExact?_isSome_of_dvd hg hdvd'

end

end HexPolyZGcdMathlib
