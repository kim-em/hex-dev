/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality.Order
public import HexArith.Montgomery.Context
-- For the `#guard` regression block only: the interpreter needs IR for the
-- trial-division cross-check.
meta import HexArith.Nat.Prime

public section

/-!
The Miller-Rabin test as an untrusted filter with a proved compositeness
direction.

`millerRabin n a = false` proves `¬ Prime n` through
`not_prime_of_millerRabin_false`; `millerRabin n a = true` is evidence and
nothing more. `isProbablePrime` runs a base list and deliberately has no
completeness theorem: its call sites are searches, never proofs. The
`defaultBases` are the first 13 primes, sufficient for `n < 3.3 · 10^24` by
Sorenson-Webster; that sufficiency claim is a search heuristic and never
appears in a proof term.
-/

namespace Hex

namespace Nat

/-- Split off the factors of two: `oddSplitAux fuel m = (s, d)` with
`m = 2 ^ s * d` and `d` odd, provided the fuel bounds the number of factors
of two. -/
def oddSplitAux : Nat → Nat → Nat × Nat
  | 0, m => (0, m)
  | fuel + 1, m =>
      if m % 2 = 0 ∧ m ≠ 0 then
        let sd := oddSplitAux fuel (m / 2)
        (sd.1 + 1, sd.2)
      else (0, m)

/-- Split `m` as `2 ^ s * d` with `d` odd, returning `(s, d)`;
`oddSplit 0 = (0, 0)`. -/
def oddSplit (m : Nat) : Nat × Nat := oddSplitAux (m.log2 + 1) m

private theorem oddSplitAux_spec :
    ∀ fuel m, m ≠ 0 → m < 2 ^ fuel →
      2 ^ (oddSplitAux fuel m).1 * (oddSplitAux fuel m).2 = m ∧
        (oddSplitAux fuel m).2 % 2 = 1 := by
  intro fuel
  induction fuel with
  | zero =>
      intro m hm hlt
      simp at hlt
      omega
  | succ fuel ih =>
      intro m hm hlt
      unfold oddSplitAux
      by_cases hcase : m % 2 = 0 ∧ m ≠ 0
      · rw [ite_eq_left hcase]
        have hm2 : m / 2 ≠ 0 := by omega
        have hp2 : (2 : Nat) ^ (fuel + 1) = 2 ^ fuel + 2 ^ fuel := by
          rw [Nat.pow_succ]; omega
        have hlt2 : m / 2 < 2 ^ fuel := by omega
        obtain ⟨hprod, hodd⟩ := ih (m / 2) hm2 hlt2
        refine ⟨?_, hodd⟩
        simp only [Nat.pow_succ]
        calc 2 ^ (oddSplitAux fuel (m / 2)).1 * 2 * (oddSplitAux fuel (m / 2)).2
            = 2 ^ (oddSplitAux fuel (m / 2)).1 * (oddSplitAux fuel (m / 2)).2 * 2 := by
              rw [Nat.mul_right_comm]
          _ = m / 2 * 2 := by rw [hprod]
          _ = m := by omega
      · rw [ite_eq_right hcase]
        refine ⟨by simp, ?_⟩
        simp only []
        omega

/-- Correctness of the split: for `m ≠ 0`, `m = 2 ^ s * d` with `d` odd. -/
theorem oddSplit_spec (m : Nat) (hm : m ≠ 0) :
    2 ^ (oddSplit m).1 * (oddSplit m).2 = m ∧ (oddSplit m).2 % 2 = 1 :=
  oddSplitAux_spec _ m hm Nat.lt_log2_self

/-- The squaring loop of the strong test: starting from
`x = a ^ (2 ^ 1 * d) % n`, `true` iff some square in the next `i` steps hits
`n - 1`. -/
def mrWitnessLoop (n : Nat) : Nat → Nat → Bool
  | _, 0 => false
  | x, i + 1 => if x = n - 1 then true else mrWitnessLoop n (x * x % n) i

/-- Core of the strong test on the residue `x = a ^ d % n`, with
`n - 1 = 2 ^ s * d`. -/
def mrStrongTestCore (n s x : Nat) : Bool :=
  if x = 1 ∨ x = n - 1 then true
  else mrWitnessLoop n (x * x % n) (s - 1)

/-- The Miller-Rabin test at base `a`. `false` is a proof of compositeness;
`true` is evidence and nothing more. The branch list is part of the
specification: in particular the `a % n = 0` branch returns `true`
(inconclusive; such a base carries no information), which is what makes the
compositeness theorem true at small `n`. -/
def millerRabin (n a : Nat) : Bool :=
  if n < 2 then false
  else if n = 2 then true
  else if n % 2 = 0 then false
  else if a % n = 0 then true
  else if 1 < Nat.gcd a n then false
  else
    let split := oddSplit (n - 1)
    mrStrongTestCore n split.1 (HexArith.powMod a split.2 n)

/-- The first 13 primes: sufficient witnesses for `n < 3.3 · 10^24` by
Sorenson-Webster, a fact used only to decide what to try and never in a
proof. -/
def defaultBases : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]

/-- Run `millerRabin` over a base list. `true` proves nothing about `n`; it
is consumed only as a filter ahead of certificate construction. -/
def isProbablePrime (n : Nat) (bases : List Nat := defaultBases) : Bool :=
  bases.all (millerRabin n)

private theorem mrWitnessLoop_true_of_prime {n : Nat} (hp : Prime n)
    (h2 : 2 < n) :
    ∀ i x, x < n → x ≠ 1 → x ^ 2 ^ i % n = 1 % n →
      mrWitnessLoop n x i = true := by
  intro i
  induction i with
  | zero =>
      intro x hxn hx1 hpow
      exfalso
      rw [Nat.pow_zero, Nat.pow_one, Nat.mod_eq_of_lt hxn,
        Nat.mod_eq_of_lt (by omega : (1 : Nat) < n)] at hpow
      exact hx1 hpow
  | succ i ih =>
      intro x hxn hx1 hpow
      unfold mrWitnessLoop
      by_cases hxe : x = n - 1
      · rw [ite_eq_left hxe]
      · rw [ite_eq_right hxe]
        have h1n : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
        have hy1 : x * x % n ≠ 1 := by
          intro hy
          rcases sq_roots_of_one hp hxn (by rw [hy, h1n]) with h | h
          · exact hx1 h
          · exact hxe h
        apply ih _ (Nat.mod_lt _ (by omega)) hy1
        calc (x * x % n) ^ 2 ^ i % n
            = (x * x) ^ 2 ^ i % n := by rw [← Nat.pow_mod]
          _ = (x ^ 2) ^ 2 ^ i % n := by rw [← Nat.pow_two]
          _ = x ^ (2 * 2 ^ i) % n := by rw [← Nat.pow_mul]
          _ = x ^ 2 ^ (i + 1) % n := by rw [← Nat.pow_succ']
          _ = 1 % n := hpow

private theorem mrStrongTestCore_true_of_prime {n a s d : Nat} (hp : Prime n)
    (h2 : 2 < n) (hcop : Nat.Coprime a n)
    (hsplit : 2 ^ s * d = n - 1) (hs : 0 < s) :
    mrStrongTestCore n s (HexArith.powMod a d n) = true := by
  unfold mrStrongTestCore
  by_cases hx : HexArith.powMod a d n = 1 ∨ HexArith.powMod a d n = n - 1
  · rw [ite_eq_left hx]
  · rw [ite_eq_right hx]
    have hnpos : 0 < n := by omega
    have hxeq : HexArith.powMod a d n = a ^ d % n :=
      HexArith.powMod_eq a d n hnpos
    have h1n : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
    have hxlt : HexArith.powMod a d n < n := by
      rw [hxeq]
      exact Nat.mod_lt _ hnpos
    have hx1 : HexArith.powMod a d n ≠ 1 := fun hh => hx (Or.inl hh)
    have hxn1 : HexArith.powMod a d n ≠ n - 1 := fun hh => hx (Or.inr hh)
    have hs2 : 2 * 2 ^ (s - 1) = 2 ^ s := by
      rw [← Nat.pow_succ']
      congr 1
      omega
    apply mrWitnessLoop_true_of_prime hp h2
    · exact Nat.mod_lt _ hnpos
    · intro hy
      rcases sq_roots_of_one hp hxlt (by rw [hy, h1n]) with h | h
      · exact hx1 h
      · exact hxn1 h
    · calc (HexArith.powMod a d n * HexArith.powMod a d n % n) ^ 2 ^ (s - 1) % n
          = (HexArith.powMod a d n * HexArith.powMod a d n) ^ 2 ^ (s - 1) % n := by
            rw [← Nat.pow_mod]
        _ = (HexArith.powMod a d n ^ 2) ^ 2 ^ (s - 1) % n := by
            rw [← Nat.pow_two]
        _ = HexArith.powMod a d n ^ (2 * 2 ^ (s - 1)) % n := by
            rw [← Nat.pow_mul]
        _ = HexArith.powMod a d n ^ 2 ^ s % n := by rw [hs2]
        _ = (a ^ d % n) ^ 2 ^ s % n := by rw [hxeq]
        _ = (a ^ d) ^ 2 ^ s % n := by rw [← Nat.pow_mod]
        _ = a ^ (d * 2 ^ s) % n := by rw [← Nat.pow_mul]
        _ = a ^ (n - 1) % n := by rw [Nat.mul_comm d (2 ^ s), hsplit]
        _ = 1 % n := pow_pred_mod hp hcop

/-- A prime passes the Miller-Rabin test at every base: the contrapositive of
the compositeness theorem, proved branch by branch. -/
theorem millerRabin_eq_true_of_prime {n a : Nat} (hp : Prime n) :
    millerRabin n a = true := by
  have h2 := hp.two_le
  unfold millerRabin
  rw [ite_eq_right (by omega : ¬ n < 2)]
  by_cases hn2 : n = 2
  · rw [ite_eq_left hn2]
  rw [ite_eq_right hn2]
  have hodd : n % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one n with he | ho
    · exfalso
      rcases hp.2 2 (Nat.dvd_of_mod_eq_zero he) with h | h <;> omega
    · exact ho
  rw [ite_eq_right (by omega : ¬ n % 2 = 0)]
  by_cases ha0 : a % n = 0
  · rw [ite_eq_left ha0]
  rw [ite_eq_right ha0]
  have hgcd : Nat.gcd a n = 1 := by
    rcases hp.2 (Nat.gcd a n) (Nat.gcd_dvd_right a n) with h | h
    · exact h
    · exact absurd (Nat.mod_eq_zero_of_dvd (h ▸ Nat.gcd_dvd_left a n)) ha0
  rw [ite_eq_right (by omega : ¬ 1 < Nat.gcd a n)]
  have h2n : 2 < n := by omega
  obtain ⟨hsplit, hd⟩ := oddSplit_spec (n - 1) (by omega)
  have hs : 0 < (oddSplit (n - 1)).1 := by
    rcases Nat.eq_zero_or_pos (oddSplit (n - 1)).1 with h0 | h
    · rw [h0, Nat.pow_zero, Nat.one_mul] at hsplit
      omega
    · exact h
  exact mrStrongTestCore_true_of_prime hp h2n hgcd hsplit hs

/-- A Miller-Rabin witness proves compositeness. This is the theorem the
whole test exists for; there is deliberately no converse. -/
theorem not_prime_of_millerRabin_false {n a : Nat}
    (h : millerRabin n a = false) : ¬ Prime n := by
  intro hp
  rw [millerRabin_eq_true_of_prime hp] at h
  cases h

/-! Regression coverage: the branch table, Carmichael numbers where a Fermat
test fails and Miller-Rabin must not, base-specific strong pseudoprimes, and
agreement with trial division on an initial segment. -/

#guard millerRabin 0 2 = false
#guard millerRabin 1 2 = false
#guard millerRabin 2 5 = true
#guard millerRabin 4 2 = false
#guard millerRabin 3 3 = true    -- a ≡ 0: inconclusive, not a witness
#guard millerRabin 9 3 = false   -- shared factor
#guard millerRabin 7 2 = true
#guard millerRabin 561 2 = false   -- Carmichael
#guard millerRabin 2047 2 = true   -- strong pseudoprime to base 2
#guard millerRabin 2047 3 = false
#guard isProbablePrime 561 = false
#guard isProbablePrime 1105 = false
#guard isProbablePrime 1729 = false
#guard isProbablePrime 2465 = false
#guard isProbablePrime 6601 = false
#guard isProbablePrime 8911 = false
#guard isProbablePrime 2047 = false
#guard isProbablePrime 1373653 = false
#guard isProbablePrime 7919 = true
#guard (List.range 512).all (fun n => isProbablePrime n == isPrimeTrial n)

end Nat

end Hex
