# HexRealRootsMathlib Phase 4 branch refresh

## Accomplished

- Merged current `main` into PR #8980's branch and resolved the six overlapping
  shared-registration and fresh-module-runner conflicts.
- Kept the current generic runner and its RCF null-control, fixed-sample, and
  warm-import extensions; added only the RealRootsMathlib probe target and
  suite-specific test registrations.
- Preserved all current RCF, NumberField, Resultant, interval, conformance, and
  CI registrations while adding `HexRealRootsMathlibReplayProbe`.
- Ran the 36 generic, RealRootsMathlib, and RCF fresh-module tests, the five
  RCF comparator-driver tests, DAG checks, bench-structure lint, copyright,
  line-count, trust-surface, and diff checks successfully.
- Built `HexRealRootsMathlibReplayProbe`, `HexRCFProofProbe`, and
  `HexRCFProofProbeScientific` together; all 8,821 jobs succeeded and every
  proof-bearing probe reported exactly
  `[propext, Classical.choice, Quot.sound]`.

## Current frontier

- PR #8980 is structurally current with `main` and ready for CI and another
  independent review.
- Its scientific artifact, report, premise audit, and Phase 4 marker remain to
  be produced on the user-designated shared host.

## Next step

- Push the merge repair, obtain CI and independent review, then run the six
  balanced RealRootsMathlib probe pairs with recorded host/load/noise state and
  publish the resulting artifact and headline report.

## Blockers

- None for the branch repair.
- The host is currently heavily contended; use explicit isolation and the
  harness's recorded controls rather than discarding or mislabelling samples.
