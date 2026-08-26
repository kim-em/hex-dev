/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBasic.ExactDiv
public import HexPoly.Field

public section

/-!
Field-specialized exact division for the polynomial Smith algorithm.

This instance lives in `HexPolySmith`, rather than `HexPoly`, so the released
polynomial library retains its dependency-free boundary.  The more general
coefficient-ring instance used by subresultants remains in
`HexResultant.ExactDiv`.
-/

namespace Hex.PolyMatrix

universe u

open Hex

private theorem field_mul_div_cancel {F : Type u} [Lean.Grind.Field F]
    (a b : F) (hb : b ≠ 0) : (a * b) / b = a := by
  rw [Lean.Grind.Field.div_eq_mul_inv, Lean.Grind.Semiring.mul_assoc,
    Lean.Grind.Field.mul_inv_cancel hb, Lean.Grind.Semiring.mul_one]

private theorem field_mul_ne_zero {F : Type u} [Lean.Grind.Field F]
    (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 := by
  intro h
  rcases Lean.Grind.Field.of_mul_eq_zero h with h | h
  · exact ha h
  · exact hb h

/-- Exact polynomial division is lawful over a lightweight field. -/
instance (priority := 60) instExactDivLawsDensePolyField
    {F : Type u} [Lean.Grind.Field F] [DecidableEq F] :
    ExactDivLaws (DensePoly F) where
  mul_div_cancel_right a b hb := by
    have hbPos : 0 < b.size := by
      apply Nat.pos_of_ne_zero
      intro hsize
      exact hb ((DensePoly.size_eq_zero_iff b).mp hsize)
    have hlc : b.leadingCoeff ≠ (0 : F) :=
      DensePoly.leadingCoeff_ne_zero_of_pos_size b hbPos
    have hpair : DensePoly.divMod (a * b) b = (a, 0) :=
      DensePoly.divMod_eq_of_polynomial_mul (a * b) b a hb
        (fun x => field_mul_div_cancel x b.leadingCoeff hlc)
        (fun _ hx => field_mul_ne_zero _ _ hx hlc)
        rfl
    change (DensePoly.divMod (a * b) b).1 = a
    exact congrArg Prod.fst hpair

end Hex.PolyMatrix

namespace Hex.DensePoly

universe u

/-- `exactDiv` reconstructs a divisible numerator at every nonzero divisor. -/
theorem exactDiv_mul_eq_of_dvd {F : Type u} [Lean.Grind.Field F]
    [DecidableEq F] (p q : DensePoly F) (hq : q ≠ 0) (hdiv : q ∣ p) :
    Hex.exactDiv p q * q = p := by
  rw [Hex.exactDiv_eq_div_of_ne p hq]
  have hrec := div_mul_add_mod p q
  rw [mod_eq_zero_of_dvd p q hdiv] at hrec
  grind

end Hex.DensePoly
