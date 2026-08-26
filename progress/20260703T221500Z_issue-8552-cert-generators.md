# Issue #8552 — certifying irreducibility: compiled certificate generators

## Accomplished

Landed Part 1 of #8552: the compiled *prep* half of certifying irreducibility.

- `Berlekamp.buildIrreducibilityCertificate?` (`HexBerlekamp/Irreducibility.lean`):
  `FpPoly p → Option IrreducibilityCertificate`. Assembles the Frobenius pow
  chain (`frobeniusXPowMod k`, `k = 0..deg`) and, per maximal proper divisor
  `d` of `deg`, an extended-gcd Rabin-Bezout witness normalised so
  `left*f + right*diff = 1` (`cinv = 1/leadingCoeff (xgcd f diff).gcd`). Returns
  `none` when `rabinTest` fails. Helper `rabinBezoutWitness` factored out.
- `certifyIrreducible?` (`HexBerlekampZassenhaus/Basic.lean`):
  `ZPoly → Option ZPolyIrreducibilityCertificate`. Builds one self-verifying
  `PrimeFactorData` block per admissible small prime (Berlekamp factors + nested
  Rabin certs), greedily assigns a degree obstruction to each candidate degree,
  prunes `perPrime` to the referenced blocks (reindexing obstructions), and
  self-checks the whole certificate with `checkIrreducibleCert` before returning
  `some`. Never emits a certificate the kernel checker would reject.
- Conformance round-trip guards + a cubic-with-inert-prime positive case
  (`conformance/HexBerlekampZassenhaus/Conformance.lean`).

Neither generator carries a soundness proof (by design): correctness rides on
the existing `checkIrreducibleCert_sound`.

## Key finding (premise error, confirmed by Codex second opinion)

The issue's requirement that the ZPoly generator "must cover the
Swinnerton-Dyer case" is **not achievable with the current, soundness-proven
checker**. `checkDegreeObstructions` requires obstructing *every* degree in
`1..deg/2`, but the degree `deg/2` obstruction is essentially never available by
per-prime degree sums when the local factorization is balanced. Empirically:

- Swinnerton-Dyer `√2+√3+√5` (deg 8): obstructable degrees `[1:✓, 2:✗, 3:✓, 4:✗]`
  (every prime gives `[2,2,2,2]` or `[1×8]`).
- `Φ₁₅` (deg 8): `[1:✓, 2:✓, 3:✓, 4:✗]`.

Both are irreducible over ℤ, yet the checker can accept no certificate for them,
so the generator correctly returns `none`. Certifying them needs a stronger
obstruction (cross-prime / resultant), a checker-design change with its own
soundness proof — out of scope for a compiled generator. Documented in-code and
in the conformance guards (now assert `none` for SD/`Φ₁₅`).

## Current frontier

Part 1 builds green: `HexBerlekamp.Irreducibility`, `HexBerlekampZassenhaus.Basic`,
`HexBerlekampZassenhaus.Conformance`, and the CI-gated
`HexBerlekampZassenhausMathlib` bridge. No `sorry`/`axiom`/`native_decide` added.

## Next step (Part 2, follow-up)

- The `irreducible_cert` elaboration tactic: reify the generator output as
  literal `Expr` data and discharge `checkIrreducibleCert` via `decide +kernel`.
  Blocked on (a) certificate-tower `ToExpr`/reification (no such infrastructure
  in the repo) and a kernel-reducible integer checker
  (`checkIrreducibleCertLinear` analog), (b) Mathlib side-condition discharge
  (`IsPrimitive`, `natDegree > 0`, `Nat.Prime`) — bridges exist
  (`isPrimitive_toPolynomial_of_primitive`, `natDegree_toPolynomial`).
- Benchmark extension: `scripts/bench/kernel_factor_sweep.py` referenced by the
  issue lives only on the unmerged `kernel-decide-series` branch, not `main`.

## Blockers

None for Part 1.
