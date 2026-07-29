# HexMvPoly final hardening

## Accomplished

- Hardened the shared proof-sweep null model so its conservative envelope
  includes every observed absolute null delta, and added classifier tests for
  passing, unresolved, failed, noise-limited, unbounded, and missing-control
  paths.
- Added construction-only controls and larger terminal rungs for addition,
  collision-heavy multiplication, cancellation, SOS, and structural proof
  probes.
- Completed public correctness APIs for maximum and leading terms, degrees,
  variables, and bind, including Mathlib correspondence lemmas.
- Added a downstream kernel-replay test for `homogeneousComponent`.
- Kept the pinned SOS equality-recovery instance confined to its compatibility
  adapter after verifying that generic SOS declarations need it to select the
  transported Hex semiring structures.
- Extended the pinned-consumer runner to emit machine-readable evidence with
  exact source state, revisions, hashes, targets, Lake job counts, and build
  output hashes.
- Passed 66 sweep-harness tests and the combined `HexMvPolyTests`,
  `HexMvPolyMathlib.Correspondence`, and `HexMvPolyMathlibProofProbe` build
  (1,562 jobs).

## Current frontier

The source and harness hardening is complete. Fresh consumer-acceptance and
proof-sweep artifacts still need to be captured from this clean checkpoint.

## Next step

Run both pinned consumers and the release-quality v5 proof sweep, update the
current-state reports from those artifacts, then complete final review and PR
verification.

## Blockers

None.
