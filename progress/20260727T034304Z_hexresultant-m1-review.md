# HexResultant milestone 1 review repair

## Accomplished

- Collected the independent Claude Opus review while CI continued in parallel.
- Verified that the ambient `Zero` on the two pseudo-division correctness
  theorems was not forced to agree with `Lean.Grind.CommRing`'s zero, and
  restated the obligations over a fresh coefficient type.
- Moved pseudo-division regressions from kernel `decide` to compiled `#guard`
  checks, preserving the efficient array implementation without putting its
  indexed loops on a kernel-reduction path.
- Added independent regressions for residual scaling after a large degree
  drop, constant divisors, equal-degree inputs, the zero dividend, and both
  documented totality branches.
- Recorded the totality branches in the library SPEC and rebuilt
  `HexResultant` successfully.

## Current frontier

PR #8880 remains open with auto-merge temporarily disabled while this review
repair is committed and pushed. Its original CI run is still in progress.
The next-stage exact-division and Brown--Traub recurrence research is running
in parallel on the stacked `ResultantContract` branch.

## Next step

Push the review repair, restore squash auto-merge after the replacement CI is
green, rebase the stacked contract branch onto the reviewed milestone, and pin
the executable exact-division and subresultant recurrence contracts.

## Blockers

No implementation blocker. PR #8880 must not merge without the theorem-instance
coherence repair.
