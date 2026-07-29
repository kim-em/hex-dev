# Hex multivariate polynomial SPEC review

## Accomplished

- Ran the requested independent Claude review over documentation follow-up
  PR #9075.
- Verified each reported issue against the Lean 4.32.0-rc1 toolchain and the
  current Hex APIs.
- Corrected companion decidable-equality requirements, explicit target
  comparator arguments, the Mathlib-free derivative statement, monomial-order
  proof obligations, implementation sequencing, Phase 4 registration metadata,
  library statuses, oracle documentation, and editorial defects.
- Ran a final independent pass and corrected the literal registry syntax,
  upstream-cleanup scope, derivative instance priority, oracle mode, Lake/CI
  target registration, kernel comparator ownership, consumer aliases, and
  comparator-plot obligations it identified.
- Rejected no verified finding; the separate implementation note about equality
  is being handled in the implementation branch rather than this documentation
  commit.

## Current frontier

The revised SPEC is internally consistent enough to drive the API-stub and
consumer-compile milestones. Documentation checks pass locally. PR #9075 still
needs its updated CI run to complete before merge.

## Next step

Push the review fixes to #9075, enable auto-merge after CI, then rebase the
local core implementation commit onto the merged documentation.

## Blockers

None.
