# hex-primality: certificate search and the decision API (milestone 3c)

## Accomplished

- `HexPrimality/Search.lean` (part 2): the failure types
  (`PrimeCertStop`/`PrimeCertFailure`/`PrimeDecisionFailure`/
  `NextPrimeFailure`), `defaultPrimeFuel`, and the mutual
  fuel-plus-worklist recursion `primeCertGo`/`assembleGo` (well-founded
  on `(fuel, list length)`; these run only at runtime, so kernel
  reducibility is not a constraint). Child-certification failures are
  reported as exhaustion, never compositeness of the parent.
- `primeCert?` returns an indexed `CheckedPrimeCert` via runtime
  dependent checks, so a certificate for one number can never answer a
  request about another. `primeCert?_composite` is proved by path
  analysis over the three verdict exits (size, table completeness,
  Miller-Rabin witness), with `assembleGo_error_stop` showing search
  failures are never misreported as verdicts.
- `isPrime?` (table / trial / certificate tiers) with `isPrime?_spec`;
  total `isPrime` with the trial fallback making `isPrime_iff`
  unconditional; `nextPrime?` with the leastness invariant in
  `nextPrime?_spec`.
- Guards cover all three tiers; `2^31 - 1` exercises the certificate
  tier deterministically (its `n - 1` factors entirely over the
  committed table).

## Current frontier

Milestone 3 complete except the `primality` tactic. Milestones 4
(cube-root) and 5 (companion) and the tactic remain.

## Next step

`HexPrimality/Elab.lean`: the `primality` term/tactic elaborator.

## Blockers

Stacked on the rho PR.
