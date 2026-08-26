/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntFactor.Order
import HexPrimalityMathlib.Prime
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement

/-! Correspondence between checked natural modular orders and Mathlib's
unit-group order. -/

namespace Hex

namespace Nat

private theorem unit_pow_iff {a n k : Nat} (ha : Nat.Coprime a n) :
    (ZMod.unitOfCoprime a ha) ^ k = 1 ↔ a ^ k % n = 1 % n := by
  constructor
  · intro h
    have hv := congrArg Units.val h
    have hv' : ((a ^ k : Nat) : ZMod n) = ((1 : Nat) : ZMod n) := by
      simpa only [Units.val_pow_eq_pow_val, Units.val_one,
        ZMod.coe_unitOfCoprime, Nat.cast_pow, Nat.cast_one] using hv
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hv'
  · intro h
    apply Units.ext
    have hv : ((a ^ k : Nat) : ZMod n) = ((1 : Nat) : ZMod n) :=
      (ZMod.natCast_eq_natCast_iff' _ _ _).mpr h
    simpa only [Units.val_pow_eq_pow_val, Units.val_one,
      ZMod.coe_unitOfCoprime, Nat.cast_pow, Nat.cast_one] using hv

/-- A checked natural order is the order of the corresponding Mathlib unit. -/
theorem orderOf_eq {c : OrderCert} (h : checkOrder c = true) :
    _root_.orderOf
        (ZMod.unitOfCoprime c.base (coprime_of_checkOrder h)) = c.order := by
  let ha := coprime_of_checkOrder h
  have hn : 0 < c.modulus :=
    _root_.Nat.zero_lt_of_lt (checkOrder_one_lt_modulus h)
  apply orderOf_eq_of_pow_and_pow_div_prime (checkOrder_order_pos h)
  · apply (unit_pow_iff ha).2
    have hpow := checkOrder_pow h
    rw [HexArith.powModNat_eq _ _ _ hn] at hpow
    exact hpow
  · intro q hq hqDvd hunit
    have hqLocal : Prime q := prime_iff.mpr hq
    have hqRaw : q ∣ c.orderFac.subject := by
      simpa [checkOrder_orderFac_subject h] using hqDvd
    obtain ⟨e, he, heq⟩ :=
      (checkFactorization_primeSupport (checkOrder_orderFac h) hqLocal).mp hqRaw
    have hbad := (unit_pow_iff ha).1 hunit
    rw [← heq] at hbad
    have hne := checkOrder_pow_div_prime h e he
    rw [HexArith.powModNat_eq _ _ _ hn] at hne
    exact hne hbad

end Nat

end Hex
