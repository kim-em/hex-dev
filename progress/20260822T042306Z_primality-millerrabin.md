# hex-primality: Miller-Rabin (milestone 2b)

## Accomplished

- `HexPrimality/MillerRabin.lean`: `oddSplit` (fuel-structural, with
  `oddSplit_spec`), `mrWitnessLoop`, `mrStrongTestCore`, `millerRabin`
  with the SPEC's exact branch table (the `a % n = 0` inconclusive
  branch included; it is what makes the theorem true), `defaultBases`
  (first 13 primes), `isProbablePrime`, and the compositeness theorem
  `not_prime_of_millerRabin_false` via the contrapositive
  `millerRabin_eq_true_of_prime` (forward induction along the squaring
  loop; `sq_roots_of_one` closes the square-root escapes; Fermat in
  multiplicative form tops it off).
- No completeness theorem, per SPEC. `#guard` block: branch table
  edges, all six SPEC Carmichael numbers, base-2/base-{2,3} strong
  pseudoprimes, and agreement with `isPrimeTrial` on `[0, 512)`.

## Current frontier

Milestone 2 complete. Milestone 3 (Pocklington) can start once the
hex-arith amendments and the table are in the stack; `Hex.Rand`
(HexBasic) is the other prerequisite for the search half.

## Next step

`HexBasic/Rand.lean` (cross-SPEC, from hex-finite-field's
§Randomness), then Cert.lean.

## Blockers

Stacked on the order PR.
