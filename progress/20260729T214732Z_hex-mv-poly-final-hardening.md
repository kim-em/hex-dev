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
- Exercised the v5 validity gate on the enlarged corpus, found that SOS-8
  exceeded the allowed 2× distance from the medium null control, and added a
  same-module SOS-8 null pair before accepting any final evidence.
- Captured the final v5 sweep from clean commit `45f01eb6` with three
  magnitude-calibrated nulls and six accepted samples for all 18 pairs. The
  artifact reports `release_quality: true`, no exceptions, violations,
  preflight failures, or exhausted pairs; 52 busy preflight windows and 10
  contaminated complete attempts were rejected.
- Recorded the negative representation decision: addition, cancellation,
  SOS, and structural terminal comparisons are unresolved at the conservative
  2× threshold, while collision-heavy multiplication is a resolved failure.
- Replaced the superseded v4 artifact and updated both performance reports,
  the library threshold protocol, and the future-work representation decision.
- Passed the full 9,650-job build, focused conformance and fixture-emitter
  build, all 11 native benchmark verification targets, Phase-4, DAG, release,
  Mathlib-free bench/probe and conformance-registration checks, and 93 combined
  harness/lint tests. The local optional SymPy check skipped because SymPy is
  unavailable; release CI requires it.

## Current frontier

The implementation, reusable map layer, pinned-consumer acceptance, final
proof-sweep evidence, reports, and local verification are complete. The final
diff still needs its independent pre-PR review.

## Next step

Commit the final evidence and reports, obtain a fresh independent review,
address any findings, then open the completion PR and monitor CI to merge.

## Blockers

None.
