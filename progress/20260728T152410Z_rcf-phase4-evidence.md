# HexRCF Phase-4 evidence

## Accomplished

- Completed and independently validated the release-quality v6 proof sweep on
  `chungus2`: 19 configurations, 114 accepted pairs, 228 admitted arms, no
  exhausted pair, exact source closure, and passing 2 s / 12 s / 30 s tactic
  budgets with their preregistered budget kinds.
- Regenerated the ten compiled ladders and eleven fixed Lean/python-flint
  comparator targets from clean merged commit `f04cd955d149`, pinned to CPU 22.
  All compiled verdicts match their declared complexity, and all comparator
  hashes match `0xb`.
- Collected the five unpinned timed-region profiles required by the manifest;
  every profile passed calibration and sensitivity with zero off-thread samples
  in timed windows. Committed only the SHA-bound analysis, leaving raw captures
  developer-local as required by `SPEC/profiling.md`.
- Added the four immutable evidence artifacts and the complete headline report,
  then advanced `HexRCF.done_through` from 3 to 4.
- Completed the headline-report narratives by copying each registration-site
  complexity derivation, interpreting the monotonically diverging
  informational comparator curve, explaining every dominant profile cost, and
  restating why timed-region sampling does not apply to the proof track.
- Closed the final traceability clarifications: quantized shared-host admission,
  observed retry depth, spawn-floor and dropped-leading verdict policy,
  paired-delta semantics, timeout-cleanup evidence, and exact comparator source
  plus the observed comparator versions and a clean recreation recipe.
- Reconciled the identical proof/compiled producing trees and toolchain
  renderings, recorded shared-host load state, bounded the profile summary to
  committed fields, quantified the comparator's observed exponent gap, and
  updated the satisfied Phase-4 marker precondition in the library SPEC.
- Passed Phase-4, DAG, release-manifest, trust-surface, Mathlib-free bench/probe,
  proof-sweep unit, focused HexRCF test/probe, and HexRCF manual-chapter checks.

## Current frontier

The Phase-4 evidence branch is complete and ready to publish after closing the
report-completeness gaps. The report keeps the two genuinely unresolved
quadratic attribution deltas explicit and makes no claim beyond the committed
schedules and fixed comparator surface.

## Next step

Commit and open the final Phase-4 PR for issue #9025, obtain final independent
review and exact CI, then merge and audit the issue/PR state.

## Blockers

None.
