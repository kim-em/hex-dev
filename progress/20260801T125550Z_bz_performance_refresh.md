# Polynomial-factorization performance refresh

## Accomplished

- Generalized proposal peeling to retain every exact support-size-one-or-two
  factor exposed after the initial support-size-one-through-three sweep, while
  reusing one Hensel lift and one shared candidate budget.
- Required exact peeling progress before building a selected-coordinate
  proposal lattice. This retains the F190 win, removes the Wilkinson threshold
  cliff, and restores `sd6` cutoff headroom without a family-specific rule.
- Recorded clean full-corpus data for Hex, FLINT, NTL, PARI, Isabelle BZ, and
  Isabelle LLL with no early termination; every answering system agreed on
  factor degrees.
- Regenerated all 25 cactus and runtime-by-degree plots and replaced the
  historical performance narrative with current artifact provenance.
- Added CI checks that reject stale factorization measurements or plots.
- Verified a 376/392 Hex result. `hoeij_F190` is newly solved in 7.215 seconds,
  `sd6` answers in 7.866 seconds, and the common-row median above one
  millisecond is 0.995x versus the preceding clean baseline.
- Passed the complete 9,711-job root build, Berlekamp--Zassenhaus conformance,
  source/data freshness checking, deterministic regeneration of all 25 plots,
  and the no-new-axiom-or-sorry diff check.

## Current frontier

- The source, measurements, figures, and reports are ready for independent
  review, PR CI, and merge.
- Cross-prime reachable-degree filtering is the next evidence-backed general
  optimization candidate; the planner already caches the required bitsets.

## Next step

- Obtain an independent review, then create, monitor, and merge the PR.

## Blockers

- None.
