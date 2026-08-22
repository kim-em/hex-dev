# hex-primality-mathlib: the correspondence layer (milestone 5a)

## Accomplished

- Scaffolded `HexPrimalityMathlib` (default-target lean_lib, umbrella,
  libraries.yml entry active, CI lib target; the SPEC's yaml block
  updated to the landed statuses).
- `Prime.lean`: `prime_iff` (one lemma, `prime_iff_forall_lt` against
  `Nat.prime_def_lt`), and the `Nat.Prime`-flavoured transports:
  `natPrime_of_checkPrime`, `natPrime_of_checkPrimeAt` (what the
  `Nat.Prime` tactic handler will emit), `isPrime_iff_natPrime`,
  `not_natPrime_of_millerRabin_false`, `nextPrime?_natPrime`. No
  `DecidablePred Nat.Prime` instance, per SPEC.
- `Segment.lean`: `primeTable_spec`, `primesIn_spec`,
  `filter_prime_range` over `Finset.range`, and `forall_prime_lt`, the
  scaffold for "every prime below x satisfies P" statements.

## Current frontier

Milestone 5's remaining piece is the norm_num extension and the
`Nat.Prime` goal handler for the `primality` tactic.

## Next step

PR16: NormNum.lean and the tactic handler.

## Blockers

Stacked on the pock3 PR.
