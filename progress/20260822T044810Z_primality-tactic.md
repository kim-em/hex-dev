# hex-primality: the primality tactic (milestone 3 complete)

## Accomplished

- `HexPrimality/Elab.lean`: `primality n` term elaborator and the
  three tactic forms, following the `irreducibility` architecture:
  defeq transparency check on the literal, bit budget, compiled
  `primeCert?` from the reproducible seed, verdict/exhaustion
  diagnostics (witness base named on compositeness; seed, attempts,
  fuel on exhaustion), untrusted-search self-check with the same
  compiled `checkPrime` the kernel replays, and the emitted term
  `prime_of_checkPrimeAt nE (reified certificate) (Eq.refl true)` so
  the kernel replays only the checker.
- The reifier is pure constructor applications over `Nat` literals
  (no proof slots inside the certificate, by the subject-readoff
  design). The companion will register an additional
  `@[tactic primalityTac]` handler for `Nat.Prime` goals; the
  mechanism is noted in the module docstring.
- In-module elaboration tests: every syntax form across the table,
  trial, and certificate tiers (`2^31 - 1` kernel-replays a two-level
  certificate), and `#guard_msgs` on the two failure messages.

## Current frontier

Milestone 3 is complete. Remaining: the sieve (milestone 1's second
half), the cube-root variant (milestone 4), the companion (milestone
5), conformance, and bench.

## Next step

Cert3.lean: the Brillhart-Lehmer-Selfridge m = 1 theorem.

## Blockers

Stacked on the decision-API PR.
