/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.Cert3
public import HexPrimality.Order
public import HexPrimality.Table
public import HexArith.Montgomery.Context
-- For the `#guard` regression block only.
meta import HexPrimality.Table
meta import HexArith.Montgomery.Context

public section

/-!
The Pocklington primality certificate, its kernel-replayable checker, and
checker soundness.

`PrimeCert` is one inductive: a stored-table leaf, the square-root
Pocklington node, and the cube-root Brillhart-Lehmer-Selfridge node. Both
Pocklington arms check their arithmetic conditions and recursively replay
every child certificate. The prime of each factor entry is not stored; it is
read off as the child certificate's subject, which removes a redundancy an
attacker could otherwise exploit.

The checker-owned definitions are `@[expose]` and structurally recursive. The
replay closure runs through `HexArith.powModNat` (the kernel-facing
specification whose `@[csimp]` twin takes the Montgomery path at runtime),
core `Nat` arithmetic including `Nat.gcd`, `Nat.mod`, and `Nat.div`, and the
table's exposed binary search. The `decide +kernel` probes in
`HexBench.PrimalityKernel` confirm that accepted certificates in both
Pocklington forms replay by kernel reduction alone. `prime_of_checkPrime`
proves soundness of both arms; per the SPEC, no certificate-existence,
checker-completeness, or search-completeness claim accompanies it.
-/

namespace Hex

namespace Nat

/-- A primality certificate. One inductive rather than two mutually
recursive declarations, because a structure referring forward to `PrimeCert`
while `PrimeCert` refers back to it does not elaborate.

Each factor entry is a base `a`, an exponent `e` (stored off by one, so the
exponent `e + 1` is positive by construction), and the child certificate for
a prime `q`, read off as the child's subject. Factor lists in both Pocklington
constructors must be in strictly ascending child-subject order for the checker
to accept them. -/
inductive PrimeCert where
  /-- `n` is an entry of the stored table. -/
  | small (n : Nat)
  /-- Pocklington: `factors` partially factors `n - 1` past its square
  root. -/
  | pock (n : Nat) (factors : List (Nat × Nat × PrimeCert))
  /-- The cube-root Brillhart-Lehmer-Selfridge variant, with the cofactor
  decomposition `R = 2 F s + r` and the integer-square-root witness `w` for
  the discriminant test (`Nat.sqrt` is well-founded recursion and does not
  kernel-reduce, so the checker verifies `w` instead of computing a root). -/
  | pock3 (n r s w : Nat) (factors : List (Nat × Nat × PrimeCert))
deriving Repr

/-- The number a certificate is about. -/
@[expose]
def PrimeCert.subject : PrimeCert → Nat
  | .small n | .pock n _ | .pock3 n _ _ _ _ => n

/-- `acc * q ^ e`, checking each nonzero multiplication by division before
constructing it. A zero accumulator or base returns zero immediately; otherwise
the computation aborts as soon as the next product would exceed `bound`, so an
attacker-chosen enormous power is never constructed. -/
@[expose]
def boundedPowMul (bound q : Nat) : Nat → Nat → Option Nat
  | acc, 0 => some acc
  | acc, e + 1 =>
      if acc = 0 then some 0
      else if q = 0 then some 0
      else if acc ≤ bound / q then boundedPowMul bound q (acc * q) e
      else none

/-- The factored part `F = ∏ qᵢ ^ (eᵢ + 1)` of a factor list, aborting as
soon as the running product exceeds `bound`. -/
@[expose]
def certProduct (bound : Nat) : List (Nat × Nat × PrimeCert) → Option Nat
  | [] => some 1
  | (_, e, c) :: rest =>
      match boundedPowMul bound c.subject 1 (e + 1) with
      | none => none
      | some pw =>
          match certProduct bound rest with
          | none => none
          | some f => boundedPowMul bound f pw 1

/-- Continue the canonical factor-subject check above a strict lower bound. -/
@[expose]
def subjectsAfter (lower : Nat) : List (Nat × Nat × PrimeCert) → Bool
  | [] => true
  | (_, _, c) :: rest =>
      decide (lower < c.subject) && subjectsAfter c.subject rest

/-- Structural check on the factor list: every claimed prime is at least
`2`, and the claimed primes are in strictly ascending order. The canonical
order implies pairwise distinctness with one lower-bound subject comparison
per entry. -/
@[expose]
def subjectsOk (factors : List (Nat × Nat × PrimeCert)) : Bool :=
  subjectsAfter 1 factors

/-- The per-entry witness conditions: Fermat at the base, and the gcd
condition at the reduced exponent. The gcd argument is written modularly:
the checker only holds the residue `x`, and `(x + n - 1) % n` is `x - 1`
modulo `n` at every residue, where the literal `x - 1` would truncate at
`x = 0`. -/
@[expose]
def checkWitness (n q a : Nat) : Bool :=
  HexArith.powModNat a (n - 1) n == 1 % n &&
    Nat.gcd ((HexArith.powModNat a ((n - 1) / q) n + n - 1) % n) n == 1

/-- The arithmetic side of the square-root Pocklington node: `n` odd and at
least `2`, canonical strictly ascending factor subjects, `F ∣ n - 1` with
`n < F * F`, and every per-entry witness condition. Child certificates are
checked separately by `checkPrime`. -/
@[expose]
def checkPockArith (n : Nat) (factors : List (Nat × Nat × PrimeCert)) : Bool :=
  decide (2 ≤ n) && n % 2 == 1 && subjectsOk factors &&
    match certProduct (n - 1) factors with
    | none => false
    | some F =>
        (n - 1) % F == 0 && decide (n < F * F) &&
          factors.all fun x => checkWitness n x.2.2.subject x.1

/-- The arithmetic side of the cube-root node: everything the square-root
arm verifies except the `n < F * F` bound, which the
Brillhart-Lehmer-Selfridge conditions replace: `F` even, the cofactor
`R = (n - 1) / F` odd (the weaker form of the classical `gcd(F, R) = 1`
that the proof uses once `F` is even), the decomposition `R = 2Fs + r` with
`1 ≤ r < 2F`, the cube-root size bound, and the discriminant condition on
`r² - 8s`, with the stored witness `w` verifying non-squareness by two
multiplications. (When `r² ≤ 8s` the truncated subtraction makes the
witness clause `w * w < 0` unsatisfiable, so the disjunct is simply never
taken; the middle disjunct covers that region.) -/
@[expose]
def checkPock3Arith (n r s w : Nat)
    (factors : List (Nat × Nat × PrimeCert)) : Bool :=
  decide (2 ≤ n) && n % 2 == 1 && subjectsOk factors &&
    match certProduct (n - 1) factors with
    | none => false
    | some F =>
        (n - 1) % F == 0 && F % 2 == 0 && (n - 1) / F % 2 == 1 &&
          (n - 1) / F == 2 * F * s + r &&
          decide (1 ≤ r) && decide (r < 2 * F) &&
          decide (n < (F + 1) * (2 * F * F + (r - 1) * F + 1)) &&
          (s == 0 || decide (r * r < 8 * s) ||
            (decide (w * w < r * r - 8 * s) &&
              decide (r * r - 8 * s < (w + 1) * (w + 1)))) &&
          factors.all fun x => checkWitness n x.2.2.subject x.1

mutual

/-- Accept or reject a primality certificate. Pocklington factor lists are
accepted only in strictly ascending child-subject order. Structurally recursive
and fully `@[expose]`d, so acceptance replays by kernel reduction alone. -/
@[expose]
def checkPrime : PrimeCert → Bool
  | .small n => isTablePrime n
  | .pock n factors => checkPockArith n factors && checkChildren factors
  | .pock3 n r s w factors =>
      checkPock3Arith n r s w factors && checkChildren factors

/-- Accept every child certificate of a factor list. -/
@[expose]
def checkChildren : List (Nat × Nat × PrimeCert) → Bool
  | [] => true
  | (_, _, c) :: rest => checkPrime c && checkChildren rest

end

/-! Accumulator lemmas -/

/-- On success, the bounded accumulator computes the ordinary product. -/
theorem boundedPowMul_eq {bound q : Nat} :
    ∀ (e acc r : Nat), boundedPowMul bound q acc e = some r →
      r = acc * q ^ e := by
  intro e
  induction e with
  | zero =>
      intro acc r h
      unfold boundedPowMul at h
      injection h with h
      subst h
      simp
  | succ e ih =>
      intro acc r h
      unfold boundedPowMul at h
      by_cases ha : acc = 0
      · rw [ite_eq_left ha] at h
        injection h with h
        subst h
        simp [ha]
      · rw [ite_eq_right ha] at h
        by_cases hq : q = 0
        · rw [ite_eq_left hq] at h
          injection h with h
          subst h
          simp [hq]
        · rw [ite_eq_right hq] at h
          by_cases hb : acc ≤ bound / q
          · rw [ite_eq_left hb] at h
            rw [ih (acc * q) r h, Nat.pow_succ, Nat.mul_assoc,
              Nat.mul_comm q (q ^ e)]
          · rw [ite_eq_right hb] at h
            cases h

/-- A successful bounded multiplication preserves the accumulator bound. The
incoming bound is needed only for the zero-exponent case; every positive step
establishes it before constructing the next accumulator. -/
theorem boundedPowMul_le {bound q acc e r : Nat} (hacc : acc ≤ bound)
    (h : boundedPowMul bound q acc e = some r) : r ≤ bound := by
  induction e generalizing acc r with
  | zero =>
      unfold boundedPowMul at h
      injection h with h
      simpa [h] using hacc
  | succ e ih =>
      unfold boundedPowMul at h
      by_cases ha : acc = 0
      · rw [ite_eq_left ha] at h
        injection h with h
        subst h
        exact Nat.zero_le _
      · rw [ite_eq_right ha] at h
        by_cases hq : q = 0
        · rw [ite_eq_left hq] at h
          injection h with h
          subst h
          exact Nat.zero_le _
        · rw [ite_eq_right hq] at h
          by_cases hb : acc ≤ bound / q
          · rw [ite_eq_left hb] at h
            exact ih ((Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hq)).mp hb) h
          · rw [ite_eq_right hb] at h
            cases h

/-- A successful certificate product is bounded when its initial accumulator
`1` is bounded. -/
theorem certProduct_le {bound : Nat} (hbound : 1 ≤ bound) :
    ∀ (l : List (Nat × Nat × PrimeCert)) (F : Nat),
      certProduct bound l = some F → F ≤ bound := by
  intro l F h
  cases l with
  | nil =>
      unfold certProduct at h
      injection h with h
      simpa [h] using hbound
  | cons a rest =>
      obtain ⟨a1, e, c⟩ := a
      unfold certProduct at h
      split at h
      · cases h
      next pw hpw =>
        split at h
        · cases h
        next f hcp =>
          exact boundedPowMul_le (boundedPowMul_le hbound hpw) h

/-- The unbounded product the accumulator computes when it does not abort. -/
private def certProd : List (Nat × Nat × PrimeCert) → Nat
  | [] => 1
  | (_, e, c) :: rest => c.subject ^ (e + 1) * certProd rest

private theorem certProduct_eq {bound : Nat} :
    ∀ (l : List (Nat × Nat × PrimeCert)) (F : Nat),
      certProduct bound l = some F → F = certProd l := by
  intro l
  induction l with
  | nil =>
      intro F h
      unfold certProduct at h
      injection h with h
      subst h
      rfl
  | cons a rest ih =>
      intro F h
      obtain ⟨a1, e, c⟩ := a
      unfold certProduct at h
      split at h
      · cases h
      next pw hpw =>
        split at h
        · cases h
        next f hcp =>
          have h1 := boundedPowMul_eq (e + 1) 1 pw hpw
          have h2 := ih f hcp
          have h3 := boundedPowMul_eq 1 pw F h
          simpa [certProd, h1, h2] using h3

private theorem subjectsAfter_spec :
    ∀ (lower : Nat) (l : List (Nat × Nat × PrimeCert)),
      subjectsAfter lower l = true →
        (∀ x ∈ l, lower < x.2.2.subject) ∧
          l.Pairwise (fun a b => a.2.2.subject < b.2.2.subject)
  | _, [], _ => ⟨by simp, List.Pairwise.nil⟩
  | lower, a :: rest, h => by
      obtain ⟨a1, e, c⟩ := a
      unfold subjectsAfter at h
      rw [Bool.and_eq_true, decide_eq_true_iff] at h
      have ih := subjectsAfter_spec c.subject rest h.2
      refine ⟨?_, List.pairwise_cons.mpr ⟨ih.1, ih.2⟩⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h.1
      · exact Nat.lt_trans h.1 (ih.1 x hx)

private theorem subjectsAfter_mono {lower upper : Nat} (hlu : lower ≤ upper) :
    ∀ (l : List (Nat × Nat × PrimeCert)), subjectsAfter upper l = true →
      subjectsAfter lower l = true
  | [], _ => by simp [subjectsAfter]
  | a :: rest, h => by
      obtain ⟨a1, e, c⟩ := a
      unfold subjectsAfter at h ⊢
      simp only [Bool.and_eq_true, decide_eq_true_iff] at h ⊢
      exact ⟨Nat.lt_of_le_of_lt hlu h.1, h.2⟩

private theorem subjectsOk_cons {a : Nat × Nat × PrimeCert}
    {rest : List (Nat × Nat × PrimeCert)}
    (h : subjectsOk (a :: rest) = true) :
    2 ≤ a.2.2.subject ∧ (∀ x ∈ rest, x.2.2.subject ≠ a.2.2.subject) ∧
      subjectsOk rest = true := by
  obtain ⟨a1, e, c⟩ := a
  unfold subjectsOk subjectsAfter at h
  rw [Bool.and_eq_true, decide_eq_true_iff] at h
  have htail := subjectsAfter_spec c.subject rest h.2
  refine ⟨?_, ?_, ?_⟩
  · change 2 ≤ c.subject
    omega
  · intro x hx
    exact Nat.ne_of_gt (htail.1 x hx)
  · unfold subjectsOk
    exact subjectsAfter_mono (by omega) rest h.2

private theorem subjectsOk_forall :
    ∀ {l : List (Nat × Nat × PrimeCert)}, subjectsOk l = true →
      ∀ x ∈ l, 2 ≤ x.2.2.subject := by
  intro l
  induction l with
  | nil =>
      intro _ x hx
      cases hx
  | cons a rest ih =>
      intro h x hx
      obtain ⟨ha2, _, hrest⟩ := subjectsOk_cons h
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact ha2
      · exact ih hrest x hx'

private theorem dvd_pow_self'' (a : Nat) {k : Nat} (hk : k ≠ 0) : a ∣ a ^ k := by
  cases k with
  | zero => exact absurd rfl hk
  | succ k => exact ⟨a ^ k, by rw [Nat.pow_succ, Nat.mul_comm]⟩

private theorem checkChildren_forall :
    ∀ {l : List (Nat × Nat × PrimeCert)}, checkChildren l = true →
      ∀ x ∈ l, checkPrime x.2.2 = true := by
  intro l
  induction l with
  | nil =>
      intro _ x hx
      cases hx
  | cons a rest ih =>
      intro h x hx
      obtain ⟨a1, e, c⟩ := a
      unfold checkChildren at h
      rw [Bool.and_eq_true] at h
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact h.1
      · exact ih h.2 x hx'

/-! Prime-power combination -/

private theorem prime_eq_of_dvd {p q : Nat} (hp : Prime p) (hq : Prime q)
    (h : p ∣ q) : p = q := by
  rcases hq.2 p h with h1 | h1
  · exact absurd h1 (by have := hp.two_le; omega)
  · exact h1

private theorem coprime_certProd {q : Nat} (hq : Prime q) :
    ∀ {l : List (Nat × Nat × PrimeCert)},
      (∀ x ∈ l, Prime x.2.2.subject) → (∀ x ∈ l, x.2.2.subject ≠ q) →
      Nat.Coprime q (certProd l) := by
  intro l
  induction l with
  | nil =>
      intro _ _
      exact Nat.coprime_one_right q
  | cons a rest ih =>
      intro hprime hne
      obtain ⟨a1, e, c⟩ := a
      have hqc : Nat.Coprime q c.subject := by
        refine hq.coprime_of_not_dvd ?_
        intro hdvd
        exact hne _ (List.mem_cons_self ..)
          (prime_eq_of_dvd hq (hprime _ (List.mem_cons_self ..)) hdvd).symm
      have htail : Nat.Coprime q (certProd rest) :=
        ih (fun x hx => hprime x (List.mem_cons_of_mem _ hx))
          (fun x hx => hne x (List.mem_cons_of_mem _ hx))
      simpa [certProd] using Nat.Coprime.mul_right (hqc.pow_right _) htail

private theorem certProd_mem_dvd :
    ∀ {l : List (Nat × Nat × PrimeCert)} {x : Nat × Nat × PrimeCert},
      x ∈ l → x.2.2.subject ^ (x.2.1 + 1) ∣ certProd l := by
  intro l
  induction l with
  | nil =>
      intro x hx
      cases hx
  | cons a rest ih =>
      intro x hx
      obtain ⟨a1, e, c⟩ := a
      rcases List.mem_cons.mp hx with rfl | hx'
      · exact Nat.dvd_mul_right _ _
      · exact Nat.dvd_trans (ih hx') (Nat.dvd_mul_left _ _)

/-- A product of powers of distinct primes, each dividing `m`, divides
`m`. Stated over the same fold the checker computes, so no standalone
`List.prod` API is needed. -/
private theorem certProd_dvd :
    ∀ {l : List (Nat × Nat × PrimeCert)},
      (∀ x ∈ l, Prime x.2.2.subject) → subjectsOk l = true →
      ∀ {m : Nat}, (∀ x ∈ l, x.2.2.subject ^ (x.2.1 + 1) ∣ m) →
      certProd l ∣ m := by
  intro l
  induction l with
  | nil =>
      intro _ _ m _
      exact Nat.one_dvd m
  | cons a rest ih =>
      intro hprime hsub m hdvd
      obtain ⟨h2, hne, hrest⟩ := subjectsOk_cons hsub
      obtain ⟨a1, e, c⟩ := a
      have hqprime : Prime c.subject := hprime _ (List.mem_cons_self ..)
      have hcop : Nat.Coprime (c.subject ^ (e + 1)) (certProd rest) :=
        (coprime_certProd hqprime
          (fun x hx => hprime x (List.mem_cons_of_mem _ hx))
          (fun x hx => hne x hx)).pow_left _
      have hhead : c.subject ^ (e + 1) ∣ m := hdvd _ (List.mem_cons_self ..)
      have htail : certProd rest ∣ m :=
        ih (fun x hx => hprime x (List.mem_cons_of_mem _ hx)) hrest
          (fun x hx => hdvd x (List.mem_cons_of_mem _ hx))
      simpa [certProd] using
        Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hhead htail

/-! The gcd-to-noncongruence transport -/

private theorem mod_ne_one_of_gcd {p n x : Nat} (hp : 2 ≤ p) (hpn : p ∣ n)
    (hx : x < n) (hg : Nat.gcd ((x + n - 1) % n) n = 1) :
    x % p ≠ 1 % p := by
  intro heq
  have h1p : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
  rw [h1p] at heq
  have hx1 : 1 ≤ x := by
    rcases Nat.eq_zero_or_pos x with rfl | h
    · rw [Nat.zero_mod] at heq
      omega
    · exact h
  have hpx : p ∣ x - 1 := by
    have := Nat.div_add_mod x p
    exact ⟨x / p, by omega⟩
  have hpxn : p ∣ x + n - 1 := by
    obtain ⟨u, hu⟩ := hpx
    obtain ⟨v, hv⟩ := hpn
    exact ⟨u + v, by rw [Nat.mul_add]; omega⟩
  have hpmod : p ∣ (x + n - 1) % n := by
    have h1 : p ∣ n * ((x + n - 1) / n) :=
      Nat.dvd_trans hpn (Nat.dvd_mul_right n _)
    have h2 : (x + n - 1) % n = (x + n - 1) - n * ((x + n - 1) / n) := by
      have := Nat.div_add_mod (x + n - 1) n
      omega
    rw [h2]
    exact Nat.dvd_sub hpxn h1
  have hdvd1 := Nat.dvd_gcd hpmod hpn
  rw [hg] at hdvd1
  exact absurd (Nat.dvd_one.mp hdvd1) (by omega)

/-! The Pocklington step and checker soundness -/

/-- The per-entry witness conditions give `F ∣ p - 1` for every prime
divisor `p` of `n`: each entry contributes its prime power to
`orderOf a_q p ∣ p - 1`, and the pairwise-coprime powers combine. Shared by
the square-root and cube-root soundness cases. -/
private theorem pock_divisor_step {n F : Nat}
    {factors : List (Nat × Nat × PrimeCert)} (h3 : 3 ≤ n)
    (hF : F ∣ n - 1)
    (hq : ∀ x ∈ factors, Prime x.2.2.subject)
    (hsub : subjectsOk factors = true)
    (hFprod : F = certProd factors)
    (hwit : ∀ x ∈ factors, checkWitness n x.2.2.subject x.1 = true) :
    ∀ p, Prime p → p ∣ n → F ∣ p - 1 := by
  intro p hpprime hpn
  have hp2 := hpprime.two_le
  have hnpos : 0 < n := by omega
  have hstep : ∀ x ∈ factors, x.2.2.subject ^ (x.2.1 + 1) ∣ p - 1 := by
    intro x hx
    have hw := hwit x hx
    unfold checkWitness at hw
    rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hw
    obtain ⟨hferm, hgcd⟩ := hw
    rw [HexArith.powModNat_eq _ _ _ hnpos] at hferm hgcd
    -- Transport Fermat from mod n to mod p.
    have hferm_p : x.1 ^ (n - 1) % p = 1 % p := by
      calc x.1 ^ (n - 1) % p
          = x.1 ^ (n - 1) % n % p := (Nat.mod_mod_of_dvd _ hpn).symm
        _ = 1 % n % p := by rw [hferm]
        _ = 1 % p := Nat.mod_mod_of_dvd _ hpn
    -- The gcd condition transports to noncongruence mod p.
    have hne_p : x.1 ^ ((n - 1) / x.2.2.subject) % p ≠ 1 % p := by
      have hxlt : x.1 ^ ((n - 1) / x.2.2.subject) % n < n := Nat.mod_lt _ hnpos
      have := mod_ne_one_of_gcd hp2 hpn hxlt hgcd
      intro hcontra
      apply this
      calc x.1 ^ ((n - 1) / x.2.2.subject) % n % p
          = x.1 ^ ((n - 1) / x.2.2.subject) % p := Nat.mod_mod_of_dvd _ hpn
        _ = 1 % p := hcontra
    have hpow_dvd : x.2.2.subject ^ (x.2.1 + 1) ∣ n - 1 := by
      rw [hFprod] at hF
      exact Nat.dvd_trans (certProd_mem_dvd hx) hF
    have horder := prime_pow_dvd_orderOf (hq x hx) hpow_dvd
      hpprime.one_lt hferm_p hne_p
    have hcop : Nat.Coprime x.1 p :=
      coprime_of_pow_mod_eq_one hpprime.one_lt (by omega) hferm_p
    exact Nat.dvd_trans horder (orderOf_dvd_pred hpprime hcop)
  rw [hFprod]
  exact certProd_dvd hq hsub hstep

/-- The square-root Pocklington theorem, over the checker's own data: every
prime divisor `p` of `n` satisfies `F ∣ p - 1`, so `p ≥ F + 1 > √n` and
`n` has no prime divisor at most its square root. -/
private theorem pocklington {n F : Nat}
    {factors : List (Nat × Nat × PrimeCert)} (h2 : 2 ≤ n) (hodd : n % 2 = 1)
    (hF : F ∣ n - 1) (hFF : n < F * F)
    (hq : ∀ x ∈ factors, Prime x.2.2.subject)
    (hsub : subjectsOk factors = true)
    (hFprod : F = certProd factors)
    (hwit : ∀ x ∈ factors, checkWitness n x.2.2.subject x.1 = true) :
    Prime n := by
  have h3 : 3 ≤ n := by omega
  by_cases hp : Prime n
  · exact hp
  exfalso
  obtain ⟨p, hpprime, hpn, hpsq⟩ := exists_prime_le_sqrt (by omega) hp
  have hp2 := hpprime.two_le
  have hFp : F ∣ p - 1 :=
    pock_divisor_step h3 hF hq hsub hFprod hwit p hpprime hpn
  have hFle : F ≤ p - 1 := Nat.le_of_dvd (by omega) hFp
  have hsq : F * F ≤ (p - 1) * (p - 1) := Nat.mul_le_mul hFle hFle
  have hlt : (p - 1) * (p - 1) < p * p := by
    rcases p with _ | p'
    · omega
    · have e1 : p' + 1 - 1 = p' := by omega
      rw [e1]
      have hexp : (p' + 1) * (p' + 1) = p' * p' + 2 * p' + 1 := by
        rw [Nat.add_mul, Nat.mul_add]
        omega
      omega
  omega

private theorem checkPockArith_spec {n : Nat}
    {factors : List (Nat × Nat × PrimeCert)}
    (h : checkPockArith n factors = true) :
    2 ≤ n ∧ n % 2 = 1 ∧ subjectsOk factors = true ∧
      ∃ F, F = certProd factors ∧ F ∣ n - 1 ∧ n < F * F ∧
        ∀ x ∈ factors, checkWitness n x.2.2.subject x.1 = true := by
  unfold checkPockArith at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h2, hodd⟩, hm⟩ := h
  rw [Bool.and_eq_true] at h2
  obtain ⟨h2', hodd'⟩ := h2
  split at hm
  · cases hm
  next F hprod =>
    rw [Bool.and_eq_true, Bool.and_eq_true] at hm
    obtain ⟨⟨hdvd, hlt⟩, hall⟩ := hm
    refine ⟨by simpa using h2', by simpa using hodd', hodd,
      F, certProduct_eq _ _ hprod,
      Nat.dvd_of_mod_eq_zero (by simpa using hdvd),
      by simpa using hlt, ?_⟩
    rw [List.all_eq_true] at hall
    intro x hx
    exact hall x hx

private theorem checkPock3Arith_spec {n r s w : Nat}
    {factors : List (Nat × Nat × PrimeCert)}
    (h : checkPock3Arith n r s w factors = true) :
    2 ≤ n ∧ n % 2 = 1 ∧ subjectsOk factors = true ∧
      ∃ F, F = certProd factors ∧ F ∣ n - 1 ∧ F % 2 = 0 ∧
        (n - 1) / F % 2 = 1 ∧ (n - 1) / F = 2 * F * s + r ∧
        1 ≤ r ∧ r < 2 * F ∧
        n < (F + 1) * (2 * F * F + (r - 1) * F + 1) ∧
        (s = 0 ∨ r * r < 8 * s ∨ ∀ t, t * t ≠ r * r - 8 * s) ∧
        ∀ x ∈ factors, checkWitness n x.2.2.subject x.1 = true := by
  unfold checkPock3Arith at h
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨h2, hodd⟩, hm⟩ := h
  rw [Bool.and_eq_true] at h2
  obtain ⟨h2', hodd'⟩ := h2
  split at hm
  · cases hm
  next F hprod =>
    simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_iff,
      beq_iff_eq, List.all_eq_true] at hm
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨hdvd, heven⟩, hrodd⟩, hdec⟩, hr1⟩, hr2⟩, hbound⟩,
      hdisc⟩, hall⟩ := hm
    refine ⟨by simpa using h2', by simpa using hodd', hodd,
      F, certProduct_eq _ _ hprod, Nat.dvd_of_mod_eq_zero hdvd,
      heven, hrodd, hdec, hr1, hr2, hbound, ?_, hall⟩
    rcases hdisc with (hs0 | hlt) | ⟨hw1, hw2⟩
    · exact Or.inl hs0
    · exact Or.inr (Or.inl hlt)
    · exact Or.inr (Or.inr (not_square_of_sqrt_witness hw1 hw2))

private theorem prime_of_checkPrime_aux :
    ∀ N c, PrimeCert.subject c = N → checkPrime c = true → Prime N := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro c hsubj hcheck
    cases c with
    | small m =>
        have hm : m = N := hsubj
        subst hm
        unfold checkPrime at hcheck
        exact mem_primeTable_prime (isTablePrime_iff.mp hcheck)
    | pock m factors =>
        have hm : m = N := hsubj
        subst hm
        unfold checkPrime at hcheck
        rw [Bool.and_eq_true] at hcheck
        obtain ⟨harith, hchildren⟩ := hcheck
        obtain ⟨h2, hodd, hsub, F, hFprod, hFdvd, hFF, hwit⟩ :=
          checkPockArith_spec harith
        have hchildprime : ∀ x ∈ factors, Prime x.2.2.subject := by
          intro x hx
          have hcheckx := checkChildren_forall hchildren x hx
          have hq2 : 2 ≤ x.2.2.subject := subjectsOk_forall hsub x hx
          have hqltm : x.2.2.subject < m := by
            have hqdvd : x.2.2.subject ∣ m - 1 := by
              refine Nat.dvd_trans ?_ hFdvd
              rw [hFprod]
              exact Nat.dvd_trans (dvd_pow_self'' _ (by omega))
                (certProd_mem_dvd hx)
            have hm3 : 3 ≤ m := by omega
            have := Nat.le_of_dvd (by omega : 0 < m - 1) hqdvd
            omega
          exact ih x.2.2.subject hqltm x.2.2 rfl hcheckx
        exact pocklington h2 hodd hFdvd hFF hchildprime hsub hFprod hwit
    | pock3 m r s w factors =>
        have hm : m = N := hsubj
        subst hm
        unfold checkPrime at hcheck
        rw [Bool.and_eq_true] at hcheck
        obtain ⟨harith, hchildren⟩ := hcheck
        obtain ⟨h2, hodd, hsub, F, hFprod, hFdvd, hFeven, hRodd, hdec, hr1,
          hr2, hbound, hdisc, hwit⟩ := checkPock3Arith_spec harith
        have hF0 : 0 < F := by
          rcases Nat.eq_zero_or_pos F with h0 | h
          · subst h0
            have := Nat.eq_zero_of_zero_dvd hFdvd
            omega
          · exact h
        have hchildprime : ∀ x ∈ factors, Prime x.2.2.subject := by
          intro x hx
          have hcheckx := checkChildren_forall hchildren x hx
          have hq2 : 2 ≤ x.2.2.subject := subjectsOk_forall hsub x hx
          have hqltm : x.2.2.subject < m := by
            have hqdvd : x.2.2.subject ∣ m - 1 := by
              refine Nat.dvd_trans ?_ hFdvd
              rw [hFprod]
              exact Nat.dvd_trans (dvd_pow_self'' _ (by omega))
                (certProd_mem_dvd hx)
            have hm3 : 3 ≤ m := by omega
            have := Nat.le_of_dvd (by omega : 0 < m - 1) hqdvd
            omega
          exact ih x.2.2.subject hqltm x.2.2 rfl hcheckx
        exact pocklington3 (by omega) hFdvd hFeven hF0 hRodd hdec hr1 hr2
          hbound hdisc
          (pock_divisor_step (by omega) hFdvd hchildprime hsub hFprod hwit)

/-- Checker soundness: an accepted certificate proves its subject prime.
The whole conclusion; no certificate-existence, checker-completeness, or
search-completeness claim accompanies it. -/
theorem prime_of_checkPrime {c : PrimeCert} (h : checkPrime c = true) :
    Prime c.subject :=
  prime_of_checkPrime_aux _ c rfl h

/-- Single-Bool-slot wrapper for the tactic reifier: the kernel verifies the
subject match and the certificate replay in one reduction. -/
theorem prime_of_checkPrimeAt {n : Nat} {c : PrimeCert}
    (h : (c.subject == n && checkPrime c) = true) : Prime n := by
  rw [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1 ▸ prime_of_checkPrime h.2

/-- An accepted certificate tied to the number requested by its caller. The
subject equality is load-bearing: `checkPrime` proves primality of
`c.subject`, not of an unrelated input that happened to request `c`. -/
structure CheckedPrimeCert (n : Nat) where
  /-- The certificate itself. -/
  raw : PrimeCert
  /-- The certificate is about the requested number. -/
  subject_eq : raw.subject = n
  /-- The checker accepts. -/
  valid : checkPrime raw = true

/-- The primality of the requested subject. -/
theorem CheckedPrimeCert.prime {n : Nat} (c : CheckedPrimeCert n) : Prime n :=
  c.subject_eq ▸ prime_of_checkPrime c.valid

/-! Regression coverage: table leaves, accepted Pocklington nodes, explicit
zero and truncating-division boundaries for bounded multiplication, structural
preflight on long canonical lists and late malformed entries, and rejected
certificates covering the arithmetic clauses and adversarial products. The
checker's negative cases matter as much as its positive ones, and no oracle
produces them. -/

set_option maxRecDepth 100000   -- table walks in the guards below

/-- A long canonical factor list for the linear structural-preflight guards. -/
private def longFactors : List (Nat × Nat × PrimeCert) :=
  (List.range 2048).map fun i => (0, 0, .small (i + 2))

#guard subjectsOk longFactors = true
#guard subjectsOk (longFactors ++ [(0, 0, .small 2049)]) = false

#guard checkPrime (.small 97) = true
#guard checkPrime (.small 100) = false
#guard checkPrime (.small 100003) = false  -- prime, but above the table bound
#guard checkPrime (.pock 7 [(2, 0, .small 3)]) = true
#guard checkPrime (.pock 31 [(3, 0, .small 3), (3, 0, .small 5)]) = true
#guard checkPrime (.pock 31 [(3, 0, .small 5), (3, 0, .small 3)]) = false
  -- distinct but noncanonical subjects
#guard checkPrime (.pock 2027 [(2, 0, .small 1013)]) = true
#guard checkPrime (.pock 13 [(2, 0, .small 3)]) = false      -- F² ≤ n
#guard checkPrime (.pock 7 [(2, 0, .small 4)]) = false       -- composite factor
#guard checkPrime (.pock 7 [(6, 0, .small 3)]) = false       -- gcd witness fails
#guard checkPrime (.pock 11 [(2, 0, .small 7)]) = false      -- 7 ∤ 10
#guard boundedPowMul 0 0 1 1 = some 0                        -- zero base
#guard boundedPowMul 0 5 0 1048576 = some 0                  -- zero accumulator
#guard boundedPowMul 7 2 3 1 = some 6                        -- rounded bound accepts
#guard boundedPowMul 7 2 4 1 = none                          -- next product is 8
#guard checkPrime (.pock 7 [(2, 0, .small (2 ^ 4096))]) = false
  -- huge child subject is rejected at the first guarded product step
#guard checkPrime (.pock 97 [(5, 1048576, .small 2)]) = false
  -- huge exponent aborts when its next bounded multiplication would cross 96
#guard checkPrime (.pock 31 [(3, 0, .small 5), (3, 0, .small 7)]) = false
  -- each factor fits under 30, but their next combined product would be 35
-- Cube-root arm: n = 199 with F = 6 sits squarely in the cube-root regime
-- (F² = 36 ≤ 199 < 847 = (F+1)(2F² + (r-1)F + 1), R = 33 = 2·6·2 + 9,
-- discriminant 9² - 8·2 = 65 with witness 8² < 65 < 9²).
#guard checkPrime (.pock3 199 9 2 8 [(3, 0, .small 2), (2, 0, .small 3)]) = true
#guard checkPrime (.pock3 199 9 2 7 [(3, 0, .small 2), (2, 0, .small 3)]) = false
  -- wrong square-root witness
#guard checkPrime (.pock3 199 33 0 0 [(3, 0, .small 2), (2, 0, .small 3)]) = false
  -- r out of range
#guard checkPrime (.pock3 199 9 2 8 [(2, 0, .small 3)]) = false
  -- F = 3 odd
#guard checkPrime (.pock 199 [(3, 0, .small 2), (2, 0, .small 3)]) = false
  -- the same data fails the square-root arm: F² ≤ n

end Nat

end Hex
