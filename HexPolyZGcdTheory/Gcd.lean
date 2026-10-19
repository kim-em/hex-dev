/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyZGcd.Maximal
public import HexPolyZTheory.PolynomialEquivalence

public section

/-!
Transport of the checked integer-polynomial gcd API to Mathlib's
`Polynomial ℤ` representation.
-/

namespace HexPolyZGcdTheory

open Hex

noncomputable section

/-- The transported checked gcd divides the left input. -/
theorem gcd_dvd_left (f h : ZPoly) :
    HexPolyZTheory.equiv (ZPoly.gcd f h) ∣ HexPolyZTheory.equiv f := by
  simpa only [HexPolyZTheory.equiv_apply] using
    HexPolyTheory.toPolynomial_dvd (ZPoly.gcd_dvd_left f h)

/-- The transported checked gcd divides the right input. -/
theorem gcd_dvd_right (f h : ZPoly) :
    HexPolyZTheory.equiv (ZPoly.gcd f h) ∣ HexPolyZTheory.equiv h := by
  simpa only [HexPolyZTheory.equiv_apply] using
    HexPolyTheory.toPolynomial_dvd (ZPoly.gcd_dvd_right f h)

/-- Every common executable divisor divides the transported checked gcd. -/
theorem dvd_gcd (d f h : ZPoly)
    (hdf : HexPolyZTheory.equiv d ∣ HexPolyZTheory.equiv f)
    (hdh : HexPolyZTheory.equiv d ∣ HexPolyZTheory.equiv h) :
    HexPolyZTheory.equiv d ∣ HexPolyZTheory.equiv (ZPoly.gcd f h) := by
  have hdf' : d ∣ f := by
    exact HexPolyTheory.toPolynomial_dvd_iff.mp (by
      simpa only [HexPolyZTheory.equiv_apply] using hdf)
  have hdh' : d ∣ h := by
    exact HexPolyTheory.toPolynomial_dvd_iff.mp (by
      simpa only [HexPolyZTheory.equiv_apply] using hdh)
  simpa only [HexPolyZTheory.equiv_apply] using
    HexPolyTheory.toPolynomial_dvd (ZPoly.dvd_gcd d f h hdf' hdh')

/-- Checked coprime cofactors establish greatestness after transport to
Mathlib polynomials. -/
theorem coprimeCofactors_greatest {f h g : ZPoly}
    (hc : ZPoly.CoprimeCofactors f h g) (d : ZPoly)
    (hdf : HexPolyZTheory.equiv d ∣ HexPolyZTheory.equiv f)
    (hdh : HexPolyZTheory.equiv d ∣ HexPolyZTheory.equiv h) :
    HexPolyZTheory.equiv d ∣ HexPolyZTheory.equiv g := by
  have hdf' : d ∣ f := HexPolyTheory.toPolynomial_dvd_iff.mp (by
    simpa only [HexPolyZTheory.equiv_apply] using hdf)
  have hdh' : d ∣ h := HexPolyTheory.toPolynomial_dvd_iff.mp (by
    simpa only [HexPolyZTheory.equiv_apply] using hdh)
  simpa only [HexPolyZTheory.equiv_apply] using
    HexPolyTheory.toPolynomial_dvd
      (ZPoly.dvd_gcd_of_coprimeCofactors hc d hdf' hdh')

/-- Checked exact division succeeds precisely for a nonzero divisor that
divides after transport to Mathlib polynomials. -/
theorem divExact?_eq_dvd (f g : ZPoly) :
    (ZPoly.divExact? f g).isSome = true ↔
      g ≠ 0 ∧ HexPolyZTheory.equiv g ∣ HexPolyZTheory.equiv f := by
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
        · apply HexPolyTheory.toPolynomial_dvd
          refine ⟨q, ?_⟩
          rw [DensePoly.mul_comm_poly]
          exact (ZPoly.divExact?_product hq).symm
  · rintro ⟨hg, hdvd⟩
    have hdvd' : g ∣ f := HexPolyTheory.toPolynomial_dvd_iff.mp (by
      simpa only [HexPolyZTheory.equiv_apply] using hdvd)
    exact ZPoly.divExact?_isSome_of_dvd hg hdvd'

end

end HexPolyZGcdTheory
