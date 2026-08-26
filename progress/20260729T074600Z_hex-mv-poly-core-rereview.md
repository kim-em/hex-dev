# Hex multivariate polynomial core re-review

## Accomplished

- Rebased PR #9077 onto the current `main` and completed a clean independent
  re-review of the amended merge candidate.
- Moved `HexMvPoly.KernelTests` out of the release-manifest-backed
  `HexReleaseTests` target into the unpublished-library target
  `HexMvPolyTests`.
- Registered that build-only target in CI and both DAG/alignment allowlists.
- Lowered the unfinished `IsMonomialOrder` instances below the proved storage
  instances and verified with `#print axioms` that a concrete polynomial value
  does not depend on `sorryAx`.
- Ran the release manifest, published trust-surface, DAG, Phase 4, and
  `HexMvPolyTests` checks successfully.

## Current frontier

- PR #9077 is ready for its final CI run and merge once the fix commit is
  pushed.
- Eleven proof obligations remain explicitly reserved for later milestones.
- The reusable `ExtTreeMap` extension requested during review has not yet been
  added.

## Next step

- Push the re-review fix and arm auto-merge for PR #9077.
- On the follow-up branch, add an upstreamable `ExtTreeMap` operations module
  and refactor polynomial addition to consume it before continuing with
  multiplication and conformance.

## Blockers

- None.
