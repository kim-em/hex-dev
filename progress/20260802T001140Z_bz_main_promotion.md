# Polynomial-factorization main promotion

## Accomplished

- Opened the missing promotion PR from `release-conformance-runtime` to `main`.
- Merged the intervening Lean 4.33 and release-sync changes into the promotion
  branch without conflicts.
- Rebuilt the public Hex factorization service and recorded a clean complete
  392-row Hex sweep on `chungus2`; the external comparator records remain
  current and were reused.
- Regenerated all 25 cactus and runtime-by-degree figures and updated the
  current performance reports for the Lean 4.33 measurement.
- Verified source/data freshness, cross-system factor-degree agreement, and
  byte-for-byte figure regeneration locally.

## Current frontier

- The promotion branch contains current `main`, the general proposal-peeling
  work, fresh Hex measurements, and regenerated figures.
- PR #9124 needs a fresh complete CI run after the promotion-refresh commit.

## Next step

- Commit and push the refresh, monitor the exact Actions job state, and confirm
  the auto-merge lands in `main` after CI passes.

## Blockers

- None.
