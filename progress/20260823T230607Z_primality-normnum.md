# hex-primality-mathlib: norm_num and the Nat.Prime tactic reach

## Accomplished

- `HexPrimality/Elab.lean`: `provePrime` generalized to
  `provePrimeWith head`, and the bare tactic now defers root
  `Nat.Prime` goal shapes (unsupported-syntax) so a companion handler
  on the same syntax kind can take them.
- `HexPrimalityMathlib/NormNum.lean`: the certificate-backed
  `norm_num` extension (`evalNatPrimeCert`): below
  `natPrimeCertThreshold` it defers; above, positive verdicts emit the
  reified certificate through `natPrime_of_checkPrimeAt` and negative
  verdicts a validated rho factor through Mathlib's `deriveNotPrime`;
  hard-semiprime exhaustion fails silently. The `Nat.Prime` goal
  handler for `primality` registers on the shared syntax kind.
- Dispatch finding, documented in the module: `norm_num` consults
  extensions in registration order and Mathlib's trial-division
  extension registers first, succeeding at elaboration on large
  numerals with minFac chains the kernel cannot check past ~25 bits;
  extension erasure does not persist across imports, so the fix is
  per-file opt-in (`attribute [-norm_num] ...evalNatPrime`) with the
  re-registered `evalNatPrimeTrial` alias keeping small numerals
  working. `NormNumTests.lean` exercises the pattern: certificate and
  rho verdicts at 31 bits, alias trial division below the threshold.
  Three namespace-resolution traps fixed along the way (`Nat.Prime`
  inside any `Hex.*` namespace, including dotted `def` names,
  resolves to `Hex.Nat.Prime`, affecting attribute patterns).
- `by primality` remains the caveat-free vehicle for large numerals
  on both predicates.

## Current frontier

Milestone 5 complete. Remaining: the sieve (milestone 1's second
half), conformance, and bench.

## Next step

PR17: conformance fixtures and the PARI oracle.

## Blockers

Stacked on the companion PR.
