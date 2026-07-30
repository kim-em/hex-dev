# HexMvPoly release audit

## Accomplished

- Audited the publish-time dependency closure of `HexMvPoly` and
  `HexMvPolyMathlib`.
- Confirmed that the computational library depends only on the Mathlib-free
  `HexBasic` and `HexPoly` packages and has no native system dependency.
- Identified the release-manifest, standalone-test, repository-skeleton,
  first-sync, and fresh-clone verification steps.
- Confirmed that the SOS compatibility façade currently imports
  `HexMvPolyMathlib`, so either both split libraries must be published or the
  façade must be refactored before switching away from the monorepo pin.

## Current frontier

The source, READMEs, SPEC, benchmarks, conformance drivers, fixture, SymPy
oracle, and consumer validation are release-ready. `HexMvPoly` and
`HexMvPolyMathlib` are not yet registered in
`scripts/release/released.yml`, and `HexMvPoly.KernelTests` remains in the
explicit pre-release Lake target.

## Next step

Bootstrap the two destination repository skeletons, add both libraries to the
publish manifest and aggregate pins, move `HexMvPoly.KernelTests` into the
release-backed target, validate the manifest and full build, then run the sync
dry before the first real publish.

## Blockers

The current GitHub identity cannot resolve either intended destination
repository, so repository creation or access must exist before the sync can
clone and populate them.
