# HexMvPoly release layout

## Accomplished

- Added `hex-mv-poly` and `hex-mv-poly-mathlib` to the publish-out manifest in
  dependency order, including aggregate pins and the core kernel regression
  target.
- Moved the combined core SPEC into the per-library publish location and added
  a dedicated Mathlib-bridge SPEC.
- Moved the shared benchmark corpus under `bench/HexMvPoly/` so the ordinary
  benchmark mapping publishes a self-contained project, then updated all
  monorepo and comparator imports.
- Promoted `HexMvPoly.KernelTests` into the manifest-backed
  `HexReleaseTests` target and removed the temporary unpublished-library
  target.
- Updated release bootstrap documentation for the two new repositories.
- Passed the release-manifest checker, DAG checker, full 9,650-job
  `lake build`, benchmark and emitter builds, exact fixture reproduction, and
  all 59 SymPy oracle cases.

## Current frontier

The source-of-truth tree is release-shaped and green. The two GitHub
repositories still need their unmanaged first-commit skeletons before the
publish workflow can clone and populate them.

## Next step

Commit and open the hex-dev release-preparation PR, bootstrap and validate both
destination repositories, attach the `hex` team, then run the publish workflow
dry and real.

## Blockers

None.
