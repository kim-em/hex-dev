/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyZ.IntegerPolynomial

public section
set_option backward.proofsInPublic true

/-!
Checked exact division for integer dense polynomials.

This is the shared primitive used by integer-polynomial gcd and by
Berlekamp--Zassenhaus recombination.  The latter adds its own policy about
rejecting unit candidates; exact division itself accepts every nonzero exact
divisor, including units.
-/

namespace Hex.ZPoly

/-- The exact quotient `f / g`, or `none` when `g = 0` or the executable
integer-polynomial division does not reconstruct `f` exactly. -/
@[expose]
def divExact? (f g : ZPoly) : Option ZPoly :=
  if g.isZero then
    none
  else
    let qr := DensePoly.divMod f g
    if qr.2 = 0 && qr.1 * g == f then
      some qr.1
    else
      none

/-- Division by the zero polynomial is always rejected. -/
@[simp] theorem divExact?_zero_right (f : ZPoly) : divExact? f 0 = none := by
  have hz : (0 : ZPoly).isZero = true := by rfl
  unfold divExact?
  rw [hz]
  simp

/-- A successful exact division carries the checked multiplication witness. -/
theorem divExact?_product
    {f g q : ZPoly} (h : divExact? f g = some q) : q * g = f := by
  unfold divExact? at h
  split at h
  · contradiction
  · generalize hqr : DensePoly.divMod f g = qr at h
    cases qr with
    | mk quotient remainder =>
        simp only at h
        split at h
        · rename_i hcheck
          cases h
          exact (by
            simpa [Bool.and_eq_true, beq_iff_eq] using hcheck :
              remainder = 0 ∧ q * g = f).2
        · contradiction

/-- Long division returns the witnessed quotient for every exact multiple by
a nonzero integer polynomial. -/
theorem divMod_eq_mul_of_ne_zero
    (f g q : ZPoly) (hg : g ≠ 0) (hmul : q * g = f) :
    DensePoly.divMod f g = (q, 0) := by
  have hgpos : 0 < g.size := by
    rcases Nat.lt_or_ge 0 g.size with hpos | hzero
    · exact hpos
    · exfalso
      apply hg
      exact (DensePoly.size_eq_zero_iff g).mp (Nat.eq_zero_of_le_zero hzero)
  have hlc_ne : g.leadingCoeff ≠ 0 :=
    DensePoly.leadingCoeff_ne_zero_of_pos_size g hgpos
  apply DensePoly.divMod_eq_of_polynomial_mul f g q hg
  · intro a
    exact Int.mul_ediv_cancel a hlc_ne
  · intro a ha
    exact Int.mul_ne_zero ha hlc_ne
  · exact hmul

/-- Exact division succeeds exactly on a supplied multiplication witness when
the divisor is nonzero. -/
theorem divExact?_eq {f g q : ZPoly} (hg : g ≠ 0) :
    divExact? f g = some q ↔ f = q * g := by
  constructor
  · intro h
    exact (divExact?_product h).symm
  · intro hmul
    have hgpos : 0 < g.size := by
      rcases Nat.lt_or_ge 0 g.size with hpos | hzero
      · exact hpos
      · exfalso
        apply hg
        exact (DensePoly.size_eq_zero_iff g).mp (Nat.eq_zero_of_le_zero hzero)
    have hisZero : g.isZero = false := by
      unfold DensePoly.isZero
      have hsize : g.coeffs.size ≠ 0 := by
        change g.size ≠ 0
        exact Nat.ne_of_gt hgpos
      simpa [Array.isEmpty_iff_size_eq_zero] using hsize
    have hdiv : DensePoly.divMod f g = (q, 0) :=
      divMod_eq_mul_of_ne_zero f g q hg hmul.symm
    unfold divExact?
    rw [hisZero, hdiv]
    simp [hmul]

/-- Every nonzero divisor is found by the executable exact-division check. -/
theorem divExact?_isSome_of_dvd {f g : ZPoly} (hg : g ≠ 0) :
    g ∣ f → (divExact? f g).isSome := by
  rintro ⟨q, hq⟩
  have hmul : f = q * g := by
    rw [DensePoly.mul_comm_poly]
    exact hq
  have hsome : divExact? f g = some q := (divExact?_eq hg).2 hmul
  rw [hsome]
  rfl

/-! Kernel regressions cover exact, inexact, unit, negative-unit, and
zero-divisor behavior. -/

example :
    divExact? (DensePoly.ofList [2, 4, 2]) (DensePoly.ofList [1, 1]) =
      some (DensePoly.ofList [2, 2]) := by
  decide

example :
    divExact? (DensePoly.ofList [2, 4, 2]) (DensePoly.ofList [1, 2]) = none := by
  decide

example (f : ZPoly) : divExact? f 1 = some f := by
  exact (divExact?_eq (by decide)).2 (by rw [DensePoly.mul_one_right_poly])

example :
    divExact? (DensePoly.ofList [2, -4]) (DensePoly.C (-1)) =
      some (DensePoly.ofList [-2, 4]) := by
  decide

example (f : ZPoly) : divExact? f 0 = none := divExact?_zero_right f

end Hex.ZPoly
