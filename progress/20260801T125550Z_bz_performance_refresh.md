# Polynomial-factorization performance refresh

## Accomplished

- Generalized proposal peeling to retain every exact support-size-one-or-two
  factor exposed after the initial support-size-one-through-three sweep, while
  reusing one Hensel lift and one shared candidate budget.
- Required exact peeling progress before building a selected-coordinate
  proposal lattice. This retains the F190 coverage gain, leaves the measured
  Wilkinson curve within about seven percent of its prior values, and restores
  `sd6` coverage without a family-specific rule.
- Recorded clean full-corpus data for Hex, FLINT, NTL, PARI, Isabelle BZ, and
  Isabelle LLL with no early termination; every answering system agreed on
  factor degrees.
- Regenerated all 25 cactus and runtime-by-degree plots and replaced the
  historical performance narrative with current artifact provenance.
- Added CI checks that reject stale factorization measurements or plots.
- Verified a 376/392 Hex result. `hoeij_F190` is newly solved in 7.369 seconds,
  `sd6` answers in 7.963 seconds, and the common-row median above one
  millisecond is 0.997x versus the preceding clean baseline.
- Passed the complete 9,711-job root build, Berlekamp--Zassenhaus conformance,
  source/data freshness checking, deterministic regeneration of all 25 plots,
  and the no-new-axiom-or-sorry diff check.
- Recorded the expected proposal-count change in the trace fixture and baseline:
  the 24-root replay case now counts all 24 cheap exact-division proposals.
- Addressed the independent review by removing duplicate obstruction searches
  after rejected certificate primes, tightening report claims to the committed
  evidence, documenting the CI policy, and cross-checking newest-per-system
  answers even when their measurements live in separate artifacts.
- Replaced the superseded Hex records with a clean post-review 392-row sweep and
  regenerated all 25 figures from that record.

## Current frontier

- The source, measurements, figures, and reports have passed independent review
  and are ready for PR CI and merge.
- Cross-prime reachable-degree filtering is the next evidence-backed general
  optimization candidate; the planner already caches the required bitsets.

## Next step

- Create the PR, monitor its exact Actions job state, and merge after CI passes.

## Blockers

- None.
