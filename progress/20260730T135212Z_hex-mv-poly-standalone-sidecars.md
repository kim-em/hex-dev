# HexMvPoly standalone sidecars

## Accomplished

- Diagnosed the first standalone `hex-mv-poly` CI failure as a Lake module
  ownership collision: sidecar modules under the `HexMvPoly.*` prefix were
  also resolved against the required core package.
- Renamed the shared conformance fixtures and benchmark corpus to the distinct
  top-level modules `HexMvPolyFixtures` and `HexMvPolyCorpus`.
- Extended the release manifest API with explicit `conformance_files` and
  `bench_files` mappings so reusable sidecar modules publish with their owning
  library without becoming computational-library source.
- Updated the Mathlib proof-probe support import to the renamed benchmark
  corpus.
- Published the current `hex-test-kit`, which supplies the multivariate
  polynomial JSON emit helpers required by the standalone conformance driver.
- Validated the standalone root/tests, conformance build, exact committed
  fixture regeneration, emitter build, and all 11 benchmark verification
  cases.
- Ran the release-manifest and dependency-DAG checks, the proof-probe target,
  and the full 9,650-job monorepo build successfully.

## Current frontier

The packaging fix is ready for a focused follow-up PR. The already published
`hex-mv-poly` commit predates these sidecar module-name fixes.

## Next step

Merge the follow-up, sync `hex-mv-poly` again from the new monorepo `main`,
then repin and republish `hex-mv-poly-mathlib`, the `hex` aggregate, and SOS to
the final release commits.

## Blockers

The existing Actions release PAT is restricted to its pre-existing repository
selection and cannot push the newly created repos. The same guarded sync driver
works with the authenticated CLI credential, including the live
compare-and-swap baseline, so release work can continue safely.
