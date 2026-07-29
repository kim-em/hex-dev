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
- Addressed the final independent review: made `HexMvPolyMathlib.aeval` and
  `eval₂Hom` direct executable homomorphisms, removed explicit
  `DecidableEq` requirements from the transported ring/algebra structures,
  and removed the pinned SOS adapter's blanket equality instance.
- Preserved SOS's exact legacy `aeval` implicit-argument order while routing
  its bundled `eval₂Hom` through the public direct implementation. The cached
  pinned SOS suite still passes all 1,545 jobs and CompPoly passes all 1,902.
- Added downstream kernel guards for nonidentity `eval₂`, `reorder`, `rename`,
  and `subst`; updated the shared HexRCF harness test for the v7/robust-null-v2
  contract; and corrected the registry snapshot to Phase 7.
- Disclosed the measurement-rule evolution, non-budget-maximal terminal
  rungs, and historical native/comparator corpus mismatch. The representation
  conclusion is now stated narrowly: the positive gate was not demonstrated,
  so `ExtTreeMap` remains the default; the data do not show that the sorted
  alternative is slower.
- Re-ran the full 9,650-job build, 1,563-job companion/proof-probe build,
  focused conformance and fixture emission, all 11 native verification
  targets, 119 combined harness tests, Phase-4, DAG, release, Mathlib-free
  bench/probe, and conformance-registration checks successfully.

## Current frontier

The implementation, reusable map layer, final review fixes, reports, and local
verification are complete. Exact evidence recaptures are still needed because
the public bridge and shared collision corpus changed after the existing
clean-source artifacts.

## Next step

Commit the review fixes, recapture pinned-consumer, kernel, native, and
comparator evidence from that clean source state, refresh their reports and
plots, then open the completion PR and monitor CI to merge.

## Blockers

None.
