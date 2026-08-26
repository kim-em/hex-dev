/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntFactor.Divisors
public import HexPrimality.Order

public section

/-! Multiplicative-order, primitive-root, and Carmichael certificates. -/

namespace Hex

namespace Nat

/-- A raw witness that `base` has exactly `order` modulo `modulus`. -/
structure OrderCert where
  base : Nat
  modulus : Nat
  order : Nat
  orderFac : Factorization
deriving Repr

/-- Replay an exact multiplicative-order certificate. -/
@[expose]
def checkOrder (c : OrderCert) : Bool :=
  decide (1 < c.modulus) && decide (0 < c.order) &&
    decide (c.orderFac.subject = c.order) &&
    checkFactorization c.orderFac &&
    decide (HexArith.powModNat c.base c.order c.modulus = 1 % c.modulus) &&
    c.orderFac.factors.all fun e =>
      decide (HexArith.powModNat c.base (c.order / e.prime) c.modulus ≠
        1 % c.modulus)

/-- Order data accepted by the checker. -/
structure CheckedOrderCert where
  raw : OrderCert
  valid : checkOrder raw = true

private theorem checkOrder_parts {c : OrderCert} (h : checkOrder c = true) :
    1 < c.modulus ∧ 0 < c.order ∧ c.orderFac.subject = c.order ∧
      checkFactorization c.orderFac = true ∧
      HexArith.powModNat c.base c.order c.modulus = 1 % c.modulus ∧
      ∀ e ∈ c.orderFac.factors,
        HexArith.powModNat c.base (c.order / e.prime) c.modulus ≠
          1 % c.modulus := by
  simpa only [checkOrder, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, and_assoc] using h

/-- An accepted order certificate has a nontrivial modulus. -/
theorem checkOrder_modulus {c : OrderCert} (h : checkOrder c = true) :
    1 < c.modulus :=
  (checkOrder_parts h).1

/-- An accepted order certificate has positive claimed order. -/
theorem checkOrder_order_pos {c : OrderCert} (h : checkOrder c = true) :
    0 < c.order :=
  (checkOrder_parts h).2.1

/-- The factorization in an accepted order certificate targets its order. -/
theorem checkOrder_factorization_subject {c : OrderCert}
    (h : checkOrder c = true) : c.orderFac.subject = c.order :=
  (checkOrder_parts h).2.2.1

/-- The factorization in an accepted order certificate is valid. -/
theorem checkOrder_factorization {c : OrderCert} (h : checkOrder c = true) :
    checkFactorization c.orderFac = true :=
  (checkOrder_parts h).2.2.2.1

/-- The claimed order in an accepted certificate sends the base to one. -/
theorem checkOrder_pow {c : OrderCert} (h : checkOrder c = true) :
    HexArith.powModNat c.base c.order c.modulus = 1 % c.modulus :=
  (checkOrder_parts h).2.2.2.2.1

/-- Removing any listed prime divisor from an accepted claimed order does not
send the base to one. -/
theorem checkOrder_prime_divisor {c : OrderCert} (h : checkOrder c = true) :
    ∀ e ∈ c.orderFac.factors,
      HexArith.powModNat c.base (c.order / e.prime) c.modulus ≠
        1 % c.modulus :=
  (checkOrder_parts h).2.2.2.2.2

private theorem prime_dvd_pow' {q a : Nat} (hq : Prime q) :
    ∀ {k : Nat}, q ∣ a ^ k → q ∣ a := by
  intro k
  induction k with
  | zero =>
      intro h
      simp only [Nat.pow_zero] at h
      exact absurd (Nat.dvd_one.mp h) hq.ne_one
  | succ k ih =>
      intro h
      rw [Nat.pow_succ] at h
      exact (hq.dvd_mul.mp h).elim ih id

private theorem prime_dvd_factorProduct {q : Nat} (hq : Prime q) :
    ∀ {entries : List PrimePower},
      (∀ e ∈ entries, Prime e.prime) →
      q ∣ (entries.map fun e => e.prime ^ e.exponent).prod →
      ∃ e ∈ entries, e.prime = q := by
  intro entries hprime hdvd
  induction entries with
  | nil =>
      simp only [List.map_nil, List.prod_nil] at hdvd
      exact absurd (Nat.dvd_one.mp hdvd) hq.ne_one
  | cons e rest ih =>
      simp only [List.map_cons, List.prod_cons] at hdvd
      rcases hq.dvd_mul.mp hdvd with he | hr
      · have he' : q ∣ e.prime := prime_dvd_pow' hq he
        rcases (hprime e (by simp)).2 q he' with heq | heq
        · exact absurd heq hq.ne_one
        · exact ⟨e, by simp, heq.symm⟩
      · obtain ⟨x, hx, heq⟩ := ih (fun x hx => hprime x (by simp [hx])) hr
        exact ⟨x, by simp [hx], heq⟩

private theorem factorProduct_dvd {d : Nat} :
    ∀ {entries : List PrimePower},
      (∀ e ∈ entries, Prime e.prime) →
      entries.Pairwise (fun a b => a.prime < b.prime) →
      (∀ e ∈ entries, e.prime ^ e.exponent ∣ d) →
      (entries.map fun e => e.prime ^ e.exponent).prod ∣ d := by
  intro entries hprime hsorted hdvd
  induction entries with
  | nil => simp
  | cons e rest ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [List.pairwise_cons] at hsorted
      have htailPrime : ∀ x ∈ rest, Prime x.prime := by
        intro x hx
        exact hprime x (by simp [hx])
      have hnot : ¬e.prime ∣ (rest.map fun x => x.prime ^ x.exponent).prod := by
        intro h
        obtain ⟨x, hx, heq⟩ :=
          prime_dvd_factorProduct (hprime e (by simp)) htailPrime h
        have hlt := hsorted.1 x hx
        rw [heq] at hlt
        exact Nat.lt_irrefl _ hlt
      have hcop : Nat.Coprime (e.prime ^ e.exponent)
          (rest.map fun x => x.prime ^ x.exponent).prod :=
        ((hprime e (by simp)).coprime_of_not_dvd hnot).pow_left _
      exact hcop.mul_dvd_of_dvd_of_dvd (hdvd e (by simp))
        (ih htailPrime hsorted.2 (fun x hx => hdvd x (by simp [hx])))

/-- Accepted order data identifies the local `orderOf`. -/
theorem order_eq_of_checkOrder {c : OrderCert} (h : checkOrder c = true) :
    orderOf c.base c.modulus = c.order := by
  have hp := checkOrder_parts h
  have hpow := hp.2.2.2.2.1
  rw [HexArith.powModNat_eq _ _ _ (by omega)] at hpow
  have hord_dvd : orderOf c.base c.modulus ∣ c.order :=
    orderOf_dvd_of_pow_eq_one hp.1 hp.2.1 hpow
  have hentry : ∀ e ∈ c.orderFac.factors,
      e.prime ^ e.exponent ∣ orderOf c.base c.modulus := by
    intro e he
    have heOrder : e.prime ^ e.exponent ∣ c.order := by
      rw [← hp.2.2.1]
      exact (checkFactorization_multiplicity hp.2.2.2.1 he).2 (Nat.le_refl _)
    have hne := hp.2.2.2.2.2 e he
    rw [HexArith.powModNat_eq _ _ _ (by omega)] at hne
    exact prime_pow_dvd_orderOf
      (checkFactorization_prime hp.2.2.2.1 e he) heOrder hp.1 hpow hne
  have horder_product :
      (c.orderFac.factors.map fun e => e.prime ^ e.exponent).prod ∣
        orderOf c.base c.modulus :=
    factorProduct_dvd (checkFactorization_prime hp.2.2.2.1)
      (checkFactorization_sorted hp.2.2.2.1) hentry
  have hc_dvd : c.order ∣ orderOf c.base c.modulus := by
    rw [← hp.2.2.1, ← checkFactorization_prod hp.2.2.2.1]
    exact horder_product
  exact Nat.dvd_antisymm hord_dvd hc_dvd

/-- A positive power equal to one makes the base a unit. -/
theorem coprime_of_checkOrder {c : OrderCert} (h : checkOrder c = true) :
    Nat.Coprime c.base c.modulus := by
  have hp := checkOrder_parts h
  have hpow := hp.2.2.2.2.1
  rw [HexArith.powModNat_eq _ _ _ (by omega)] at hpow
  exact coprime_of_pow_mod_eq_one hp.1 hp.2.1 hpow

/-- Test primitivity modulo a certified prime using the complete
factorization of `p - 1`. -/
def isPrimitiveRoot {p : Nat} (_pc : CheckedPrimeCert p)
    (F : CheckedFactorization (p - 1)) (g : Nat) : Bool :=
  checkOrder ⟨g, p, p - 1, F.raw⟩

/-- The checker criterion is exact. -/
theorem isPrimitiveRoot_iff {p : Nat} {pc : CheckedPrimeCert p}
    {F : CheckedFactorization (p - 1)} {g : Nat} :
    isPrimitiveRoot pc F g = true ↔ orderOf g p = p - 1 := by
  constructor
  · intro h
    exact order_eq_of_checkOrder h
  · intro horder
    have hp := pc.prime
    have hp2 := hp.two_le
    have hpred : 0 < p - 1 := by omega
    have hordPos : 0 < orderOf g p := by rw [horder]; exact hpred
    have hpow : HexArith.powModNat g (p - 1) p = 1 % p := by
      rw [HexArith.powModNat_eq _ _ _ hp.pos, ← horder]
      exact orderOf_pow_mod hordPos
    have hne : ∀ e ∈ F.raw.factors,
        HexArith.powModNat g ((p - 1) / e.prime) p ≠ 1 % p := by
      intro e he heq
      have hePrime := checkFactorization_prime F.valid e he
      have hePos := checkFactorization_exponent F.valid e he
      have hePow : e.prime ^ e.exponent ∣ p - 1 := by
        rw [← F.subject_eq]
        exact (checkFactorization_multiplicity F.valid he).2 (Nat.le_refl _)
      have heDvd : e.prime ∣ p - 1 :=
        Nat.dvd_trans (by
          simpa using Nat.pow_dvd_pow e.prime (show 1 ≤ e.exponent by omega)) hePow
      have hquotPos : 0 < (p - 1) / e.prime :=
        Nat.div_pos (Nat.le_of_dvd hpred heDvd) hePrime.pos
      have hquotLt : (p - 1) / e.prime < p - 1 :=
        Nat.div_lt_self hpred hePrime.one_lt
      apply orderOf_min hordPos _ hquotPos
      · simpa [horder] using hquotLt
      · rw [← HexArith.powModNat_eq _ _ _ hp.pos]
        exact heq
    simpa only [isPrimitiveRoot, checkOrder, Bool.and_eq_true,
      decide_eq_true_eq, List.all_eq_true, and_assoc] using
      (show 1 < p ∧ 0 < p - 1 ∧ F.raw.subject = p - 1 ∧
          checkFactorization F.raw = true ∧
          HexArith.powModNat g (p - 1) p = 1 % p ∧
          ∀ e ∈ F.raw.factors,
            HexArith.powModNat g ((p - 1) / e.prime) p ≠ 1 % p from
        ⟨hp.one_lt, hpred, F.subject_eq, F.valid, hpow, hne⟩)

private def primitiveRootGo {p : Nat} (F : CheckedFactorization (p - 1)) :
    Nat → Nat → Option (Nat × CheckedOrderCert)
  | 0, _ => none
  | fuel + 1, g =>
      if g < p then
        let raw : OrderCert := ⟨g, p, p - 1, F.raw⟩
        if h : checkOrder raw = true then some (g, ⟨raw, h⟩)
        else primitiveRootGo F fuel (g + 1)
      else none

private theorem primitiveRootGo_spec {p : Nat} {F : CheckedFactorization (p - 1)} :
    ∀ {fuel start g : Nat} {c : CheckedOrderCert},
      primitiveRootGo F fuel start = some (g, c) →
        c.raw.base = g ∧ c.raw.modulus = p ∧ c.raw.order = p - 1 := by
  intro fuel
  induction fuel with
  | zero => simp [primitiveRootGo]
  | succ fuel ih =>
      intro start g c h
      simp only [primitiveRootGo] at h
      split at h
      next hlt =>
        split at h
        next hc =>
          injection h with hpair
          simp only [Prod.mk.injEq] at hpair
          rcases hpair with ⟨rfl, rfl⟩
          simp
        next hc => exact ih h
      next hlt => contradiction

/-- Fuel-bounded ascending search for a primitive root modulo a prime. -/
def primitiveRoot? {p : Nat} (_pc : CheckedPrimeCert p)
    (F : CheckedFactorization (p - 1)) (fuel : Nat) :
    Option (Nat × CheckedOrderCert) :=
  primitiveRootGo F fuel (if p = 2 then 1 else 2)

/-- A successful primitive-root search returns an order certificate for the
requested prime and full group order. -/
theorem primitiveRoot?_spec {p : Nat} {pc : CheckedPrimeCert p}
    {F : CheckedFactorization (p - 1)} {fuel g : Nat} {c : CheckedOrderCert}
    (h : primitiveRoot? pc F fuel = some (g, c)) :
    c.raw.base = g ∧ c.raw.modulus = p ∧ c.raw.order = p - 1 := by
  exact primitiveRootGo_spec (by simpa [primitiveRoot?] using h)

/-- Carmichael value of one prime power. -/
@[expose]
def carmichaelPrimePower (e : PrimePower) : Nat :=
  if e.prime = 2 then
    if e.exponent = 1 then 1
    else if e.exponent = 2 then 2
    else 2 ^ (e.exponent - 2)
  else (e.prime - 1) * e.prime ^ (e.exponent - 1)

/-- Carmichael function from a checked complete factorization. -/
@[expose]
def carmichael {n : Nat} (F : CheckedFactorization n) : Nat :=
  F.raw.factors.foldl (fun acc e => Nat.lcm acc (carmichaelPrimePower e)) 1

private theorem pow_one_add (x r : Nat) :
    ∃ t, (1 + x) ^ r = 1 + r * x + x * x * t := by
  induction r with
  | zero => exact ⟨0, by simp⟩
  | succ r ih =>
      obtain ⟨t, ht⟩ := ih
      refine ⟨t + r + t * x, ?_⟩
      rw [Nat.pow_succ, ht]
      simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one,
        Nat.succ_mul]
      ac_rfl

private theorem one_add_of_mod {x m : Nat} (hm : 1 < m)
    (h : x % m = 1 % m) : ∃ t, x = 1 + m * t := by
  have hmod : x % m = 1 := by simpa [Nat.mod_eq_of_lt hm] using h
  refine ⟨x / m, ?_⟩
  have hsplit := Nat.mod_add_div x m
  rw [hmod] at hsplit
  omega

private theorem liftPrimePower {p x j : Nat} (hp : Prime p)
    (h : x % p ^ (j + 1) = 1 % p ^ (j + 1)) :
    x ^ p % p ^ (j + 2) = 1 % p ^ (j + 2) := by
  have hpPow : 1 < p ^ (j + 1) := by
    exact Nat.one_lt_pow (by omega) hp.one_lt
  obtain ⟨t, ht⟩ := one_add_of_mod hpPow h
  obtain ⟨s, hs⟩ := pow_one_add (p ^ (j + 1) * t) p
  rw [ht, hs]
  have hshape :
      1 + p * (p ^ (j + 1) * t) +
          (p ^ (j + 1) * t) * (p ^ (j + 1) * t) * s =
        1 + p ^ (j + 2) *
          (t + p ^ j * t * t * s) := by
    rw [show p ^ (j + 1) = p ^ j * p by simp [Nat.pow_succ],
      show p ^ (j + 2) = p ^ j * p * p by simp [Nat.pow_succ]]
    rw [Nat.mul_add]
    ac_rfl
  rw [hshape, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt]
  exact Nat.one_lt_pow (by omega) hp.one_lt

private theorem powOddPrimePower {p a : Nat} (hp : Prime p) :
    ∀ j : Nat, Nat.Coprime a (p ^ (j + 1)) →
      a ^ ((p - 1) * p ^ j) % p ^ (j + 1) = 1 % p ^ (j + 1) := by
  intro j
  induction j with
  | zero =>
      intro ha
      have hcop : Nat.Coprime a p := by simpa using ha
      simpa using pow_pred_mod hp hcop
  | succ j ih =>
      intro ha
      have hdiv : p ^ (j + 1) ∣ p ^ (j + 2) :=
        Nat.pow_dvd_pow p (by omega)
      have ha' : Nat.Coprime a (p ^ (j + 1)) :=
        Nat.Coprime.coprime_dvd_right hdiv ha
      have hlift := liftPrimePower hp (ih ha')
      simpa only [Nat.pow_mul, Nat.pow_succ, Nat.succ_eq_add_one,
        Nat.add_assoc] using hlift

private theorem mod_two_eq_one {a : Nat} (ha : Nat.Coprime a 2) :
    a % 2 = 1 := by
  rcases Nat.mod_two_eq_zero_or_one a with h | h
  · have hdvd : 2 ∣ a := Nat.dvd_of_mod_eq_zero h
    have heq : 2 = 1 := ha.symm.eq_one_of_dvd hdvd
    omega
  · exact h

private theorem oddSquareEight {a : Nat} (hodd : a % 2 = 1) :
    a ^ 2 % 8 = 1 := by
  obtain ⟨t, ht⟩ := one_add_of_mod (by decide : 1 < 2) hodd
  have heven : 2 ∣ t * (t + 1) := by
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.mul_mod]
    rcases Nat.mod_two_eq_zero_or_one t with h | h
    · simp [h]
    · have hs : (t + 1) % 2 = 0 := by omega
      simp [hs]
  obtain ⟨u, hu⟩ := heven
  have hu' : t * t + t = 2 * u := by
    rw [Nat.mul_add, Nat.mul_one] at hu
    exact hu
  have hsquare : (2 * t) * (2 * t) = 4 * (t * t) := by
    rw [show (4 : Nat) = 2 * 2 by decide]
    ac_rfl
  have hshape : (1 + 2 * t) ^ 2 = 1 + 8 * u := by
    rw [Nat.pow_two]
    simp only [Nat.mul_add, Nat.add_mul, Nat.one_mul, Nat.mul_one]
    rw [hsquare]
    omega
  rw [ht, hshape, Nat.add_mul_mod_self_left]

private theorem powTwoHigh {a : Nat} (hodd : a % 2 = 1) :
    ∀ j : Nat, a ^ (2 ^ (j + 1)) % 2 ^ (j + 3) = 1 := by
  intro j
  induction j with
  | zero => simpa using oddSquareEight hodd
  | succ j ih =>
      have hp2 : Prime 2 := by decide
      have hmod3 : 1 < 2 ^ (j + 3) :=
        Nat.one_lt_pow (by omega) (by decide)
      have ih' :
          (a ^ (2 ^ (j + 1))) % 2 ^ ((j + 2) + 1) =
            1 % 2 ^ ((j + 2) + 1) := by
        rw [show (j + 2) + 1 = j + 3 by omega, Nat.mod_eq_of_lt hmod3]
        exact ih
      have hlift := liftPrimePower (p := 2) (x := a ^ (2 ^ (j + 1)))
        (j := j + 2) hp2 ih'
      rw [← Nat.pow_mul,
        show 2 ^ (j + 1) * 2 = 2 ^ (j + 2) by
          simp only [Nat.pow_succ]] at hlift
      have hmod4 : 1 < 2 ^ ((j + 2) + 2) :=
        Nat.one_lt_pow (by omega) (by decide)
      rw [Nat.mod_eq_of_lt hmod4] at hlift
      simpa only [show (j + 2) + 2 = (j + 1) + 3 by omega,
        show (j + 1) + 1 = j + 2 by omega] using hlift

private theorem powTwoPower {a e : Nat} (he : 0 < e)
    (ha : Nat.Coprime a (2 ^ e)) :
    a ^ (if e = 1 then 1 else if e = 2 then 2 else 2 ^ (e - 2)) % 2 ^ e =
      1 % 2 ^ e := by
  have hdiv : 2 ∣ 2 ^ e := by
    simpa using Nat.pow_dvd_pow 2 (show 1 ≤ e by omega)
  have ha2 : Nat.Coprime a 2 := Nat.Coprime.coprime_dvd_right hdiv ha
  have hodd := mod_two_eq_one ha2
  rcases Nat.eq_or_lt_of_le (show 1 ≤ e by omega) with rfl | he1
  · simpa [hodd]
  rcases Nat.eq_or_lt_of_le (show 2 ≤ e by omega) with rfl | he2
  · have h8 := oddSquareEight hodd
    have hrepr := one_add_of_mod (by decide : 1 < 8) (by simpa using h8)
    obtain ⟨t, ht⟩ := hrepr
    simp only [if_neg (by decide : (2 : Nat) ≠ 1), if_pos]
    rw [ht, show 8 * t = 4 * (2 * t) by omega, Nat.add_mul_mod_self_left]
  · obtain ⟨j, rfl⟩ : ∃ j, e = j + 3 := ⟨e - 3, by omega⟩
    rw [if_neg (by omega : j + 3 ≠ 1), if_neg (by omega : j + 3 ≠ 2)]
    rw [show j + 3 - 2 = j + 1 by omega]
    have hmod : 1 < 2 ^ (j + 3) :=
      Nat.one_lt_pow (by omega) (by decide)
    simpa only [Nat.mod_eq_of_lt hmod] using powTwoHigh hodd j

private theorem powPrimePower (e : PrimePower) (hp : Prime e.prime)
    (he : 0 < e.exponent) {a : Nat}
    (ha : Nat.Coprime a (e.prime ^ e.exponent)) :
    a ^ carmichaelPrimePower e % e.prime ^ e.exponent =
      1 % e.prime ^ e.exponent := by
  by_cases hp2 : e.prime = 2
  · rw [hp2] at ha ⊢
    simpa only [carmichaelPrimePower, hp2, if_pos] using powTwoPower he ha
  · obtain ⟨j, hj⟩ : ∃ j, e.exponent = j + 1 := ⟨e.exponent - 1, by omega⟩
    rw [hj] at ha ⊢
    simpa [carmichaelPrimePower, hp2, hj] using
      powOddPrimePower hp j ha

private theorem powMultiple {a k m L : Nat}
    (h : a ^ k % m = 1 % m) (hdvd : k ∣ L) :
    a ^ L % m = 1 % m := by
  obtain ⟨t, rfl⟩ := hdvd
  calc
    a ^ (k * t) % m = (a ^ k) ^ t % m := by rw [Nat.pow_mul]
    _ = (a ^ k % m) ^ t % m := by rw [Nat.pow_mod]
    _ = (1 % m) ^ t % m := by rw [h]
    _ = 1 ^ t % m := by rw [← Nat.pow_mod]
    _ = 1 % m := by rw [Nat.one_pow]

private theorem acc_dvd_carmichaelFold :
    ∀ (entries : List PrimePower) (acc : Nat),
      acc ∣ entries.foldl (fun x y => Nat.lcm x (carmichaelPrimePower y)) acc := by
  intro entries
  induction entries with
  | nil => simp
  | cons x rest ih =>
      intro acc
      exact Nat.dvd_trans (Nat.dvd_lcm_left acc (carmichaelPrimePower x))
        (ih (Nat.lcm acc (carmichaelPrimePower x)))

private theorem carmichael_dvd_foldl (e : PrimePower) :
    ∀ {entries : List PrimePower} {acc : Nat}, e ∈ entries →
      carmichaelPrimePower e ∣
        entries.foldl (fun x y => Nat.lcm x (carmichaelPrimePower y)) acc := by
  intro entries
  induction entries with
  | nil => simp
  | cons x rest ih =>
      intro acc he
      rcases List.mem_cons.mp he with rfl | he
      · exact Nat.dvd_trans (Nat.dvd_lcm_right acc (carmichaelPrimePower e))
          (acc_dvd_carmichaelFold rest _)
      · exact ih he

/-- Carmichael's exponent sends every unit to one. -/
theorem pow_carmichael {n : Nat} (F : CheckedFactorization n)
    (a : Nat) (ha : Nat.Coprime a n) :
    a ^ carmichael F % n = 1 % n := by
  by_cases hn : n = 1
  · simpa only [hn, Nat.mod_one]
  have hnPos : 0 < n := F.pos
  have hnOne : 1 < n := by omega
  have hlocal : ∀ e ∈ F.raw.factors,
      e.prime ^ e.exponent ∣ a ^ carmichael F - 1 := by
    intro e he
    have hp := checkFactorization_prime F.valid e he
    have hePos := checkFactorization_exponent F.valid e he
    have heDvd : e.prime ^ e.exponent ∣ n := by
      rw [← F.subject_eq]
      exact (checkFactorization_multiplicity F.valid he).2 (Nat.le_refl _)
    have haLocal : Nat.Coprime a (e.prime ^ e.exponent) :=
      Nat.Coprime.coprime_dvd_right heDvd ha
    have hpow := powPrimePower e hp hePos haLocal
    have hlcm : carmichaelPrimePower e ∣ carmichael F :=
      carmichael_dvd_foldl e he
    have hpow' := powMultiple hpow hlcm
    exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hpow')
  have hprod :
      (F.raw.factors.map fun e => e.prime ^ e.exponent).prod ∣
        a ^ carmichael F - 1 :=
    factorProduct_dvd (checkFactorization_prime F.valid)
      (checkFactorization_sorted F.valid) hlocal
  have hnDvd : n ∣ a ^ carmichael F - 1 := by
    have heq := checkFactorization_prod F.valid
    rw [F.subject_eq] at heq
    simpa only [heq] using hprod
  obtain ⟨t, ht⟩ := hnDvd
  have haPos : 0 < a := by
    apply Nat.pos_of_ne_zero
    intro ha0
    subst a
    simp [Nat.Coprime] at ha
    omega
  have hshape : a ^ carmichael F = 1 + n * t := by
    have := Nat.pow_pos (n := carmichael F) haPos
    omega
  rw [hshape, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hnOne]

/-- Every multiplicative order divides the Carmichael exponent. -/
theorem orderOf_dvd_carmichael {n : Nat} (F : CheckedFactorization n)
    (a : Nat) (hn : 1 < n) (ha : Nat.Coprime a n) :
    orderOf a n ∣ carmichael F := by
  by_cases hzero : carmichael F = 0
  · simp [hzero]
  · exact orderOf_dvd_of_pow_eq_one hn (Nat.pos_of_ne_zero hzero)
      (pow_carmichael F a ha)

end Nat

end Hex
