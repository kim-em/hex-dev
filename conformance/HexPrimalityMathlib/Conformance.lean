/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimalityMathlib.OptInConformance

/-!
# HexPrimalityMathlib tactic conformance

Oracle: none; these elaboration tests construct kernel-checked proofs.
Mode: core / always.

Covered operations:

- `primality` on `Hex.Nat.Prime` and Mathlib's `Nat.Prime`
- default Mathlib `norm_num` registration
- the `use_hex_primality_norm_num` opt-in command
- thresholded trial division and positive/negative certificate-tier verdicts

Covered properties:

- positive large proofs replay Hex's checked certificate
- negative large proofs carry a proper divisor checked by the kernel
- the default registration remains Mathlib's and the opt-in is per module
- Mathlib's existing `DecidablePred Nat.Prime` instance remains selected

Covered edge cases:

- typical small prime and composite inputs
- edge inputs `0`, `1`, and both sides of the `2^24` threshold
- a 31-bit prime beyond the default trial proof's kernel-depth reach
- a strong pseudoprime as an adversarial negative input
- composite and non-literal tactic failures
-/

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
error: primality: certificate search for 11069588345001798189188705872711741673446310956174776680242876230365522527670481055399138994024099817696810905038323515123654848684366962778647276800762123 exhausted after 12 attempts (seed 11069588345001798189188705872711741673446310956174776680242876230365522527670481055399138994024099817696810905038323515123654848684366962778647276800762123, recursive fuel 512; policy maximum 512 fuel at 512 bits, 2 rho restarts with 32768 steps each); no total primality decision was attempted
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
error: primality: 561 is not prime (Miller-Rabin witness 2)
-/
#guard_msgs in
example : Nat.Prime 561 := by primality

-- No bridge-local decision instance competes with Mathlib's instance.
example : (inferInstance : DecidablePred Nat.Prime) = Nat.decidablePrime := rfl

-- Importing the opt-in tests does not import their attribute erasure: this
-- module's guarded large default failure above is also an import-boundary test.
