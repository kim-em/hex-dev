/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyZGcd.Gcd
public import HexPolyZ.Decomposition

public section
set_option backward.proofsInPublic true

/-!
Gauss descent from coprime cofactors to gcd maximality.
-/

namespace Hex

namespace ZPoly

/-- In one variable over the integers, exact coprime cofactors make their
common factor maximal.  The proof rationalizes a primitive part of `d`, uses
the field gcd laws over `Rat[x]`, and descends with
`dvd_of_toRatPoly_dvd_of_primitive`. -/
theorem dvd_gcd_of_coprimeCofactors {f h g : ZPoly}
    (hc : CoprimeCofactors f h g) (d : ZPoly)
    (hf : d ∣ f) (hh : d ∣ h) : d ∣ g := by
  sorry

/-- The public checked certificate packages coprime cofactors. -/
theorem gcdCert_coprimeCofactors (f h : ZPoly) :
    CoprimeCofactors f h (gcd f h) := by
  let cert := gcdCert f h
  have hcheck := gcdCert_checks f h
  have hcop := coprimeCofactors_of_checkGcd hcheck
  rw [gcd_eq_cert]
  exact hcop

/-- The canonical gcd divides the left input. -/
theorem gcd_dvd_left (f h : ZPoly) : gcd f h ∣ f := by
  let cert := gcdCert f h
  have hcheck := gcdCert_checks f h
  rcases checkGcd_sound hcheck with ⟨hf, _, _⟩
  refine ⟨cert.cofL, ?_⟩
  rw [gcd_eq_cert]
  exact hf

/-- The canonical gcd divides the right input. -/
theorem gcd_dvd_right (f h : ZPoly) : gcd f h ∣ h := by
  let cert := gcdCert f h
  have hcheck := gcdCert_checks f h
  rcases checkGcd_sound hcheck with ⟨_, hh, _⟩
  refine ⟨cert.cofR, ?_⟩
  rw [gcd_eq_cert]
  exact hh

/-- Every common divisor divides the canonical gcd. -/
theorem dvd_gcd (d f h : ZPoly) (hf : d ∣ f) (hh : d ∣ h) :
    d ∣ gcd f h :=
  dvd_gcd_of_coprimeCofactors (gcdCert_coprimeCofactors f h) d hf hh

end ZPoly

end Hex
