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
  have hp :
      1 < c.modulus ∧ 0 < c.order ∧ c.orderFac.subject = c.order ∧
        checkFactorization c.orderFac = true ∧
        HexArith.powModNat c.base c.order c.modulus = 1 % c.modulus ∧
        ∀ e ∈ c.orderFac.factors,
          HexArith.powModNat c.base (c.order / e.prime) c.modulus ≠
            1 % c.modulus := by
    simpa only [checkOrder, Bool.and_eq_true, decide_eq_true_eq,
      List.all_eq_true, and_assoc] using h
  let ha := coprime_of_checkOrder h
  apply orderOf_eq_of_pow_and_pow_div_prime hp.2.1
  · apply (unit_pow_iff ha).2
    have hpow := hp.2.2.2.2.1
    rw [HexArith.powModNat_eq _ _ _ (by omega)] at hpow
    exact hpow
  · intro q hq hqDvd hunit
    have hqLocal : Prime q := prime_iff.mpr hq
    have hqRaw : q ∣ c.orderFac.subject := by simpa [hp.2.2.1] using hqDvd
    obtain ⟨e, he, heq⟩ :=
      (checkFactorization_primeSupport hp.2.2.2.1 hqLocal).mp hqRaw
    have hbad := (unit_pow_iff ha).1 hunit
    rw [← heq] at hbad
    have hne := hp.2.2.2.2.2 e he
    rw [HexArith.powModNat_eq _ _ _ (by omega)] at hne
    exact hne hbad

end Nat

end Hex
