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
- Rebuilt fresh pinned SOS and CompPoly clones against clean commit `d05d0635`;
  their acceptance targets passed in 1,545 and 1,902 Lake jobs respectively,
  and the machine-readable evidence records `dirty: false`.
- Passed 66 sweep-harness tests and the combined `HexMvPolyTests`,
  `HexMvPolyMathlib.Correspondence`, and `HexMvPolyMathlibProofProbe` build
  (1,562 jobs).

## Current frontier

The source, harness hardening, and pinned-consumer acceptance are complete.
The final proof-sweep artifact still needs to be captured from a clean
checkpoint.

## Next step

Run the release-quality v5 proof sweep, update the current-state reports from
both evidence artifacts, then complete final review and PR verification.

## Blockers

None.
