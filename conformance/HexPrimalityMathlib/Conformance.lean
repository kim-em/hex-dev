/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimalityMathlib.OptInConformance
import Mathlib.Tactic.IntervalCases

/-!
# HexPrimalityMathlib conformance

Oracle: none; the bridge-local elaboration checks construct kernel-checked
proofs. Transport examples cite concrete cases from `HexPrimality.Conformance`
(whose PARI oracle mode is `if_available`) rather than recomputing those cases
as nominally independent bridge evidence.
Mode: always.

Covered operations:

- `primality` on `Hex.Nat.Prime` and Mathlib's `Nat.Prime`
- default Mathlib `norm_num` registration
- the `use_hex_primality_norm_num` opt-in command
- thresholded trial division and positive/negative certificate-tier verdicts

Covered properties and proof transports:

- `prime_iff`, checker soundness, exact decision, Miller--Rabin refutation,
  and successful next-prime results transport to Mathlib's `Nat.Prime`
- `primeTable_spec`, `primesIn_spec`, `filter_prime_range`, and
  `forall_prime_lt` expose the core segment results in Mathlib vocabulary
- positive large proofs replay Hex's checked certificate
- negative large proofs carry a proper divisor checked by the kernel
- the default registration remains Mathlib's and the opt-in is per module
- Mathlib's existing `DecidablePred Nat.Prime` instance remains selected

Covered edge cases:

- typical small prime and composite inputs
- edge inputs `0`, `1`, and both sides of the `2^24` threshold
- a 31-bit prime beyond the default trial proof's kernel-depth reach
- a strong pseudoprime as an adversarial negative input
- composite, non-literal, open-variable, and unsupported-goal tactic failures
-/

/-!
## Correspondence and transport surface

These proof-level API checks are not executable operations. Their concrete
inputs are the cases pinned in `HexPrimality.Conformance`: accepted `.pock`
and `.pock3` certificates, the decision and Miller--Rabin adversaries,
successful searches across all three tiers, and table/segment boundaries.
Executable premises remain hypotheses here so the bridge cannot turn the same
core computation into fake independent evidence.
-/

-- Predicate correspondence: typical, edge, and adversarial composite.
example : Hex.Nat.Prime 2 ↔ Nat.Prime 2 := Hex.Nat.prime_iff
example : Hex.Nat.Prime 0 ↔ Nat.Prime 0 := Hex.Nat.prime_iff
example : Hex.Nat.Prime 3215031751 ↔ Nat.Prime 3215031751 := Hex.Nat.prime_iff

-- Certificate transports use three accepted certificates checked verbatim by
-- the core conformance module; this file checks only their Mathlib transport.
example (h : Hex.Nat.checkPrime (.pock 7 [(2, 0, .small 3)]) = true) :
    Nat.Prime 7 :=
  Hex.Nat.natPrime_of_checkPrime h
example (h : Hex.Nat.checkPrime
    (.pock 31 [(3, 0, .small 3), (3, 0, .small 5)]) = true) :
    Nat.Prime 31 :=
  Hex.Nat.natPrime_of_checkPrime h
example (h : Hex.Nat.checkPrime
    (.pock3 199 9 2 8 [(3, 0, .small 2), (2, 0, .small 3)]) = true) :
    Nat.Prime 199 :=
  Hex.Nat.natPrime_of_checkPrime h

example (h : ((Hex.Nat.PrimeCert.pock 7 [(2, 0, .small 3)]).subject == 7 &&
    Hex.Nat.checkPrime (.pock 7 [(2, 0, .small 3)])) = true) : Nat.Prime 7 :=
  Hex.Nat.natPrime_of_checkPrimeAt h
example (h : ((Hex.Nat.PrimeCert.pock 31
      [(3, 0, .small 3), (3, 0, .small 5)]).subject == 31 &&
    Hex.Nat.checkPrime
      (.pock 31 [(3, 0, .small 3), (3, 0, .small 5)])) = true) :
    Nat.Prime 31 :=
  Hex.Nat.natPrime_of_checkPrimeAt h
example (h : ((Hex.Nat.PrimeCert.pock3 199 9 2 8
      [(3, 0, .small 2), (2, 0, .small 3)]).subject == 199 &&
    Hex.Nat.checkPrime
      (.pock3 199 9 2 8 [(3, 0, .small 2), (2, 0, .small 3)])) = true) :
    Nat.Prime 199 :=
  Hex.Nat.natPrime_of_checkPrimeAt h

-- Total-decision correspondence without re-running the total decision here.
example : Hex.Nat.isPrime 2 = true ↔ Nat.Prime 2 :=
  Hex.Nat.isPrime_iff_natPrime
example : Hex.Nat.isPrime 0 = true ↔ Nat.Prime 0 :=
  Hex.Nat.isPrime_iff_natPrime
example : Hex.Nat.isPrime 3215031751 = true ↔ Nat.Prime 3215031751 :=
  Hex.Nat.isPrime_iff_natPrime

-- Core conformance pins both sides of this base-specific strong-pseudoprime
-- boundary (`millerRabin 2047 2 = true`, then base 3 refutes it).
example (h : Hex.Nat.millerRabin 2047 3 = false) : ¬ Nat.Prime 2047 :=
  Hex.Nat.millerRabin_refutes_natPrime h

-- Successful-search inputs are exactly the table, trial, and certificate-tier
-- cases pinned by core conformance. Only the transport premise is abstract.
example {p : Nat} {r' : Hex.Rand}
    (h : Hex.Nat.nextPrime? 90 (Hex.Rand.ofSeed 0) 8 = .ok (p, r')) :
    90 < p ∧ Nat.Prime p ∧ ∀ q, 90 < q → q < p → ¬ Nat.Prime q :=
  Hex.Nat.nextPrime?_natPrime h
example {p : Nat} {r' : Hex.Rand}
    (h : Hex.Nat.nextPrime? 99991 (Hex.Rand.ofSeed 0) 16 = .ok (p, r')) :
    99991 < p ∧ Nat.Prime p ∧ ∀ q, 99991 < q → q < p → ¬ Nat.Prime q :=
  Hex.Nat.nextPrime?_natPrime h
example {p : Nat} {r' : Hex.Rand}
    (h : Hex.Nat.nextPrime? 10000000 (Hex.Rand.ofSeed 0) 32 = .ok (p, r')) :
    10000000 < p ∧ Nat.Prime p ∧
      ∀ q, 10000000 < q → q < p → ¬ Nat.Prime q :=
  Hex.Nat.nextPrime?_natPrime h

/-! ## Initial-segment transports -/

example : 2 ∈ Hex.Nat.primeTable ↔ Nat.Prime 2 :=
  Hex.Nat.primeTable_spec 2 (by decide)
example : 4 ∈ Hex.Nat.primeTable ↔ Nat.Prime 4 :=
  Hex.Nat.primeTable_spec 4 (by decide)
example : 99991 ∈ Hex.Nat.primeTable ↔ Nat.Prime 99991 :=
  Hex.Nat.primeTable_spec 99991 (by decide)

example : 10 ∈ Hex.Nat.primesIn 10 10 ↔
    10 ≤ 10 ∧ 10 < 10 ∧ Nat.Prime 10 :=
  Hex.Nat.primesIn_spec 10 10 10
example : 97 ∈ Hex.Nat.primesIn 90 100 ↔
    90 ≤ 97 ∧ 97 < 100 ∧ Nat.Prime 97 :=
  Hex.Nat.primesIn_spec 90 100 97
example : 100003 ∈ Hex.Nat.primesIn 99950 100050 ↔
    99950 ≤ 100003 ∧ 100003 < 100050 ∧ Nat.Prime 100003 :=
  Hex.Nat.primesIn_spec 99950 100050 100003

-- Unlike the theorem-signature checks above, these are bridge-local segment
-- computations: rewriting by the transport exposes a small, independently
-- known Mathlib `Finset` result.
set_option maxRecDepth 20000 in
example : (Finset.range 2).filter Nat.Prime = ∅ := by
  rw [Hex.Nat.filter_prime_range (by decide)]
  decide
set_option maxRecDepth 20000 in
example : (Finset.range 3).filter Nat.Prime = {2} := by
  rw [Hex.Nat.filter_prime_range (by decide)]
  decide
set_option maxRecDepth 20000 in
example : (Finset.range 10).filter Nat.Prime = {2, 3, 5, 7} := by
  rw [Hex.Nat.filter_prime_range (by decide)]
  decide

-- The universal transport consumes the table-side proof and returns a
-- statement over Mathlib's predicate.
example : ∀ p, p < 3 → Nat.Prime p → p = 2 := by
  refine Hex.Nat.forall_prime_lt (P := fun p => p = 2) (bound := 3)
    (by decide) ?_
  intro p hp hlt
  have hprime : Nat.Prime p :=
    Hex.Nat.prime_iff.mp (Hex.Nat.mem_primeTable_prime hp)
  interval_cases p <;> norm_num at hprime
  all_goals norm_num
example : ∀ p, p < 10 → Nat.Prime p → p ∈ ({2, 3, 5, 7} : Finset Nat) := by
  refine Hex.Nat.forall_prime_lt
    (P := fun p => p ∈ ({2, 3, 5, 7} : Finset Nat)) (bound := 10)
    (by decide) ?_
  intro p hp hlt
  have hprime : Nat.Prime p :=
    Hex.Nat.prime_iff.mp (Hex.Nat.mem_primeTable_prime hp)
  interval_cases p <;> norm_num at hprime
  all_goals norm_num
example : ∀ p, p < 20 → Nat.Prime p → p = 2 ∨ p % 2 = 1 := by
  refine Hex.Nat.forall_prime_lt (P := fun p => p = 2 ∨ p % 2 = 1)
    (bound := 20) (by decide) ?_
  intro p hp hlt
  have hprime : Nat.Prime p :=
    Hex.Nat.prime_iff.mp (Hex.Nat.mem_primeTable_prime hp)
  interval_cases p <;> norm_num at hprime
  all_goals norm_num

-- Ordinary imports retain pinned Mathlib's registration and small-number behavior.
example : Nat.Prime 101 := by norm_num
example : ¬ Nat.Prime 100 := by norm_num

/--
error: (kernel) deep recursion detected, use `set_option maxRecDepth <num>` to increase the limit
-/
#guard_msgs in
set_option maxRecDepth 1000 in
example : Nat.Prime 2147483647 := by norm_num

-- The bare tactic supports both predicates independently of `norm_num` registration.
example : Nat.Prime 2147483647 := by primality
example : Hex.Nat.Prime 2147483647 := by primality
example : Nat.Prime 65537 := by primality
example : Nat.Prime 9521691625768090263084389838561930764813603239089634545416648725957969250257409112878363599328138633827640729385461401574761860536478435114675541614002177 := by
  primality

/--
error: primality: certificate search for 11069588345001798189188705872711741673446310956174776680242876230365522527670481055399138994024099817696810905038323515123654848684366962778647276800762123 exhausted after 10 attempts (seed 11069588345001798189188705872711741673446310956174776680242876230365522527670481055399138994024099817696810905038323515123654848684366962778647276800762123, recursive fuel 512, root factor fuel 1030; policy maximum 512 fuel at 512 bits, 2 rho restarts with 32768 steps each); no total primality decision was attempted
-/
#guard_msgs in
example : Nat.Prime 11069588345001798189188705872711741673446310956174776680242876230365522527670481055399138994024099817696810905038323515123654848684366962778647276800762123 := by primality

/--
error: primality: input has 513 bits; the enforced policy supports at most 512 bits; raising the ceiling requires new end-to-end benchmark evidence
-/
#guard_msgs in
example : Nat.Prime 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 := by
  primality

/--
error: primality: the goal
  Nat.Prime (2 + 2)
is not about a natural-number numeral
-/
#guard_msgs in
example : Nat.Prime (2 + 2) := by primality

/--
error: primality: the argument
  n
must not contain free or meta variables
-/
#guard_msgs in
example (n : Nat) : Nat.Prime n := by primality

/--
error: primality: expected a goal of the form `Hex.Nat.Prime n` for a numeral `n` (the companion library extends this to `Nat.Prime`)
-/
#guard_msgs in
example : ¬ Nat.Prime 4 := by primality

/--
error: primality: 561 is not prime (Miller-Rabin witness 2)
-/
#guard_msgs in
example : Nat.Prime 561 := by primality

-- No bridge-local decision instance competes with Mathlib's instance.
example : (inferInstance : DecidablePred Nat.Prime) = Nat.decidablePrime := rfl

-- Importing the opt-in tests does not import their attribute erasure: this
-- module's guarded large default failure above is also an import-boundary test.
