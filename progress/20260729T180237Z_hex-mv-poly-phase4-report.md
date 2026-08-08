# HexMvPoly Phase-4 report refresh

## Accomplished

- Captured fresh filtered samply profiles for all five compiled input
  families from clean commit `23181fc7`; every profile passed calibration,
  retained-sample, off-thread-noise, confidence, and ±5 ms sensitivity
  checks.
- Replaced the stale native and comparator tables with the committed
  three-trial exports and disclosed CompPoly's fixed lexicographic storage
  comparator.
- Aligned the native narrative with the release-quality kernel decision:
  sparse addition and sum-of-squares cross the two-family gate for a future
  opt-in kernel-specialized representation.
- Recorded `HexBasic/ExtTreeMap.lean` as the upstream-candidate home for
  generic joint traversal and deletion-capable merge APIs, leaving
  coefficient combination and zero deletion as `HexMvPoly` policy.
- Removed four superseded benchmark exports after confirming that no current
  report or plotting script references them.
- Regenerated every comparator plot, passed the dependency-DAG check, and
  passed the Mathlib-free bench/proof-probe import audit.

## Current frontier

The implementation, conformance, consumer acceptance, native measurements,
kernel sweep, comparator exports, figures, and source profiles now give one
consistent Phase-4 account.

## Next step

Commit the report package, audit the Phase-5 through Phase-7 requirements
against the completed implementation, and close any remaining release
deliverables before requesting the independent review.

## Blockers

None.
