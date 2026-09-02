/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPrimality
public import Mathlib.Data.Nat.Prime.Basic

public section

/-!
The correspondence between the Mathlib-free `Hex.Nat.Prime` and Mathlib's
`Nat.Prime`, and the `Nat.Prime`-flavoured transports of the primality
surface.

`prime_iff` is the whole correspondence, and it is one lemma: the two
predicates are the same definition modulo Mathlib's `Irreducible`
packaging. Everything else transports along it.

No `DecidablePred Nat.Prime` instance is declared: Mathlib already has
`Nat.decidablePrime` with its own runtime twin, and a second global
instance would risk instance-selection churn. What this layer offers
instead is the transports here and (in a later module) the tactic and
`norm_num` reach for numerals beyond trial division.
-/

namespace Hex

namespace Nat

/-- The whole correspondence: the Mathlib-free predicate and `Nat.Prime`
agree. Everything else transports along it. -/
theorem prime_iff {n : Nat} : Prime n ↔ _root_.Nat.Prime n := by
  simpa only [Hex.Nat.Prime] using (_root_.Nat.prime_def (p := n)).symm

/-- Checker soundness, in Mathlib's vocabulary. -/
theorem natPrime_of_checkPrime {c : PrimeCert} (h : checkPrime c = true) :
    _root_.Nat.Prime c.subject :=
  prime_iff.mp (prime_of_checkPrime h)

/-- The single-Bool-slot wrapper, in Mathlib's vocabulary; what the
`Nat.Prime` tactic handler emits. -/
theorem natPrime_of_checkPrimeAt {n : Nat} {c : PrimeCert}
    (h : (c.subject == n && checkPrime c) = true) : _root_.Nat.Prime n :=
  prime_iff.mp (prime_of_checkPrimeAt h)

/-- The total decision is exact for `Nat.Prime`. -/
theorem isPrime_iff_natPrime {n : Nat} :
    isPrime n = true ↔ _root_.Nat.Prime n :=
  isPrime_iff.trans prime_iff

/-- A Miller-Rabin witness refutes `Nat.Prime`. -/
theorem millerRabin_refutes_natPrime {n a : Nat}
    (h : millerRabin n a = false) : ¬ _root_.Nat.Prime n :=
  fun hp => not_prime_of_millerRabin_false h (prime_iff.mpr hp)

/-- A successful next-prime search, in Mathlib's vocabulary. -/
theorem nextPrime?_natPrime {n : Nat} {r : Rand} {fuel p : Nat} {r' : Rand}
    (h : nextPrime? n r fuel = .ok (p, r')) :
    n < p ∧ _root_.Nat.Prime p ∧
      ∀ q, n < q → q < p → ¬ _root_.Nat.Prime q := by
  obtain ⟨hlt, hp, hmin⟩ := nextPrime?_spec h
  exact ⟨hlt, prime_iff.mp hp,
    fun q h1 h2 hq => hmin q h1 h2 (prime_iff.mpr hq)⟩

end Nat

end Hex
