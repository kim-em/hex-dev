# HexRealRootsMathlib Phase 4 review hardening

## Accomplished

- Obtained a fresh Claude Opus review of PR #8980 and verified its findings
  against the current fresh-module harness and probe manifest.
- Added baseline- and natural-degree-10 same-module null controls and fixed the
  release sweep at six balanced rounds.
- Added a direct degree-6 natural-to-refined pair so refinement cost is an
  adjacent measurement rather than a difference of unrelated medians.
- Moved the build-only modules below the collision-resistant
  `HexRealRootsMathlib.ProofProbe` namespace and split cheap CI coverage from
  the full scientific target.
- Added exact-import and source/metadata consistency tests, a versioned
  measurement identifier, and governing SPEC/manifest provenance hashes.
- Built both RealRootsMathlib probe targets successfully; every measured
  theorem reported exactly `[propext, Classical.choice, Quot.sound]`.

## Current frontier

- The structural probe branch has concrete fixes for every review finding
  that affects scientific validity.
- A separate stacked change is defining the designated-shared-host execution
  protocol requested for the actual release run.

## Next step

- Publish the review fixes to PR #8980, rerun CI and Claude review, then merge
  the structural milestone.
- Run the six-round controlled sweep on the named shared host and publish the
  artifact/report only if the null controls leave every required conclusion
  resolved.

## Blockers

- None. The shared host is being treated as an engineering constraint rather
  than a reason to defer Phase 4.
