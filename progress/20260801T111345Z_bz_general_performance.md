# Polynomial-factorization performance refresh

## Accomplished

- Reproduced the proposal-routing cliff on Wilkinson degrees 24 through 56.
- Changed direct proposal peeling to search support sizes one through three
  once, then reuse the same Hensel lift for repeated support-size-one-or-two
  peeling on exact residuals. This preserves the F190 result while restoring
  the Wilkinson curve to the classical baseline.
- Made generated irreducibility certificates check primality, primitivity, and
  positive degree at their executable boundary, and stop collecting prime
  blocks once every possible proper factor degree is obstructed.
- Added deterministic cactus-plot checking and a source-to-measurement
  freshness check to the existing single CI job.
- Verified the root build, the complete Berlekamp--Zassenhaus Mathlib bridge,
  and the Berlekamp--Zassenhaus conformance driver.

## Current frontier

- The implementation is ready for a clean-source cross-system sweep. Existing
  committed measurements and all generated plots are intentionally reported
  stale by the new checks until that sweep is committed.

## Next step

- Commit the implementation, run Hex, FLINT, PARI/GP, NTL, Isabelle BZ, and
  Isabelle LLL over the complete corpus from that clean commit, regenerate all
  figures and reports, and verify the freshness checks.

## Blockers

- None.
