/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyFp.Basic
public import Init.Grind.Ring.Field

public section

/-!
Prime-modulus field instance for `Hex.ZMod64 p`.

This module promotes the `Hex.ZMod64.PrimeModulus` typeclass witness (a
`Hex.Nat.Prime p` proof) to a `Lean.Grind.Field (Hex.ZMod64 p)` instance,
threading through the executable `ZMod64.inv` defined in
`HexModArith/Basic.lean` and the prime-modulus inverse identities from
`HexModArith/Prime.lean`.

The instance is shared between the Berlekamp factorisation pipeline and the
Berlekamp–Zassenhaus integer lift, which both previously carried an inline
copy of the construction.
-/
namespace Hex

namespace ZMod64

variable {p : Nat} [Bounds p]

@[expose]
def intPow (a : ZMod64 p) : Int → ZMod64 p
  | .ofNat n => a ^ n
  | .negSucc n => (a ^ (n + 1))⁻¹

/-- `1 ≠ 0` in `ZMod64 p` when `p` is prime. -/
theorem one_ne_zero_of_prime
    (hp : Hex.Nat.Prime p) :
    (1 : ZMod64 p) ≠ 0 := by
  intro h
  have hp2 : 2 ≤ p := hp.two_le
  have htoNat : (1 : ZMod64 p).toNat = (0 : ZMod64 p).toNat :=
    congrArg ZMod64.toNat h
  rw [show ((1 : ZMod64 p).toNat) = 1 % p from ZMod64.toNat_one,
      show ((0 : ZMod64 p).toNat) = 0 from ZMod64.toNat_zero,
      Nat.mod_eq_of_lt (by omega : 1 < p)] at htoNat
  omega

/-- The `0⁻¹ = 0` junk-value convention for `ZMod64 p`. -/
theorem inv_zero_of_zero : (0 : ZMod64 p)⁻¹ = 0 := by
  apply ZMod64.ext
  apply UInt64.toNat_inj.mp
  change (ZMod64.inv (0 : ZMod64 p)).toNat = (0 : ZMod64 p).toNat
  rw [ZMod64.toNat_inv_def]
  change (((HexArith.Int.extGcd 0 (Int.ofNat p)).2.1 % Int.ofNat p).toNat % p = 0)
  have hs := HexArith.Int.extGcd_zero_left_s_ofNat p (ZMod64.Bounds.pPos (p := p))
  rw [hs]
  simp

/-- The inverse of a nonzero residue modulo a prime is itself nonzero. -/
theorem inv_ne_zero_of_prime
    (hp : Hex.Nat.Prime p) {a : ZMod64 p} (ha : a ≠ 0) :
    a⁻¹ ≠ 0 := by
  intro hinv
  have hone := ZMod64.inv_mul_eq_one_of_prime hp ha
  change ZMod64.inv a = 0 at hinv
  rw [hinv] at hone
  have hzero : (0 : ZMod64 p) * a = 0 := by grind
  rw [hzero] at hone
  exact one_ne_zero_of_prime hp hone.symm

/-- Double-inverse identity in `ZMod64 p` for a prime modulus. -/
theorem inv_inv_of_prime
    (hp : Hex.Nat.Prime p) (a : ZMod64 p) :
    (a⁻¹)⁻¹ = a := by
  by_cases ha : a = 0
  · subst a
    rw [inv_zero_of_zero]
    exact inv_zero_of_zero
  · have hinv_ne := inv_ne_zero_of_prime hp ha
    have hleft : (a⁻¹)⁻¹ * a⁻¹ = (1 : ZMod64 p) :=
      ZMod64.inv_mul_eq_one_of_prime hp hinv_ne
    have hright : a * a⁻¹ = (1 : ZMod64 p) := by
      rw [Lean.Grind.CommSemiring.mul_comm]
      exact ZMod64.inv_mul_eq_one_of_prime hp ha
    have hprod : (((a⁻¹)⁻¹ - a) * a⁻¹) = (0 : ZMod64 p) := by
      rw [Lean.Grind.Ring.sub_eq_add_neg, Lean.Grind.Semiring.right_distrib, hleft]
      grind
    rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hprod with hdiff | hzero
    · grind
    · exact False.elim (hinv_ne hzero)

end ZMod64

/-- The `Lean.Grind.Field` instance on `Hex.ZMod64 p` carried by a
prime-modulus witness. -/
instance zmod64FieldOfPrime {p : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p] :
    Lean.Grind.Field (ZMod64 p) := by
  letI : HPow (ZMod64 p) Int (ZMod64 p) := ⟨ZMod64.intPow⟩
  refine Lean.Grind.Field.mk ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro a b
    rfl
  · intro h
    exact ZMod64.one_ne_zero_of_prime (ZMod64.PrimeModulus.prime (p := p)) h.symm
  · exact ZMod64.inv_zero_of_zero
  · intro a ha
    rw [Lean.Grind.CommSemiring.mul_comm]
    exact ZMod64.inv_mul_eq_one_of_prime (ZMod64.PrimeModulus.prime (p := p)) ha
  · intro a
    exact Lean.Grind.Semiring.pow_zero a
  · intro a n
    change a ^ (n + 1) = a ^ n * a
    exact Lean.Grind.Semiring.pow_succ a n
  · intro a n
    cases n with
    | ofNat m =>
        cases m with
        | zero =>
            show ZMod64.intPow a (-Int.ofNat 0) = (ZMod64.intPow a (Int.ofNat 0))⁻¹
            rw [show (-Int.ofNat 0) = Int.ofNat 0 by rfl]
            simp [ZMod64.intPow]
            have h1ne : (1 : ZMod64 p) ≠ 0 :=
              fun h => ZMod64.one_ne_zero_of_prime
                (ZMod64.PrimeModulus.prime (p := p)) h
            have hinv_one := ZMod64.inv_mul_eq_one_of_prime
              (ZMod64.PrimeModulus.prime (p := p)) h1ne
            rw [Lean.Grind.Semiring.mul_one] at hinv_one
            exact hinv_one.symm
        | succ m =>
            rfl
    | negSucc m =>
        simp only [Int.neg_negSucc]
        change a ^ (m + 1) = ((a ^ (m + 1))⁻¹)⁻¹
        exact (ZMod64.inv_inv_of_prime (ZMod64.PrimeModulus.prime (p := p))
          (a ^ (m + 1))).symm

end Hex
