/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimalityMathlib.Prime
import Mathlib.Data.Finset.Basic

/-!
Segment statements over the committed prime table, in the form a Mathlib
consumer states them.

`forall_prime_lt` is the scaffold for "every prime in `[1, x]` satisfies
`P`": combined with a decidable fold over the table literal it discharges
the universally quantified segment statements the SPEC calls unlocked.
-/

namespace Hex

namespace Nat

/-- The committed table lists exactly the primes below its bound. -/
theorem primeTable_spec :
    ∀ n < primeTableBound, (n ∈ primeTable ↔ _root_.Nat.Prime n) := by
  intro n hlt
  constructor
  · intro h
    exact prime_iff.mp (mem_primeTable_prime h)
  · intro h
    exact mem_primeTable_of_prime (prime_iff.mpr h) hlt

/-- Range enumeration is exact for `Nat.Prime`. -/
theorem primesIn_spec (lo hi : Nat) :
    ∀ n, n ∈ primesIn lo hi ↔ lo ≤ n ∧ n < hi ∧ _root_.Nat.Prime n := by
  intro n
  rw [mem_primesIn]
  exact and_congr_right fun _ => and_congr_right fun _ => prime_iff

/-- The `Finset` of primes below a bound inside the table's range is the
filtered table. -/
theorem filter_prime_range {bound : Nat} (h : bound ≤ primeTableBound) :
    (Finset.range bound).filter _root_.Nat.Prime =
      (primeTable.toList.filter (fun p => p < bound)).toFinset := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset,
    List.mem_filter, decide_eq_true_iff]
  constructor
  · rintro ⟨hlt, hp⟩
    exact ⟨Array.mem_def.mp
      (mem_primeTable_of_prime (prime_iff.mpr hp) (by omega)), hlt⟩
  · rintro ⟨hmem, hlt⟩
    exact ⟨hlt, prime_iff.mp (mem_primeTable_prime (Array.mem_def.mpr hmem))⟩

/-- Every-prime-below-a-bound statements reduce to a check over the table
entries. -/
theorem forall_prime_lt {P : Nat → Prop} {bound : Nat}
    (hb : bound ≤ primeTableBound)
    (h : ∀ p ∈ primeTable, p < bound → P p) :
    ∀ p, p < bound → _root_.Nat.Prime p → P p := by
  intro p hlt hp
  exact h p (mem_primeTable_of_prime (prime_iff.mpr hp) (by omega)) hlt

end Nat

end Hex
