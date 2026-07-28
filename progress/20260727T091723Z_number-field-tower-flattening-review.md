# Number-field tower flattening review

## Accomplished

- Fixed the bounded signed-shift search so a failed checked candidate advances
  to the next prescribed shift instead of aborting the whole search.
- Replaced repeated algebraic trace-product exactification with incremental
  exact gcd recovery in the accepted primitive presentation. The recovered
  coordinates remain guarded by both basis round trips.
- Added a compiled flattening regression in which the newest generator has
  absolute degree four but relative degree two.
- Reconciled the flattening SPEC with the per-step collision bound, continued
  checked search, and linear-gcd coordinate recovery, and removed the now-dead
  direct row-reduction import.
- Reduced the compiled flattening target from about 19 seconds for the original
  three regressions to about 6 seconds with the additional fourth-root
  regression included. The full repository build is green.

## Current frontier

- The flattening review's blocking control-flow finding and its main
  performance/SPEC findings are addressed locally on the flattening branch.
- The dependent conformance branch must be rebased after this fix is pushed.

## Next step

- Publish the flattening review fixes and launch a focused follow-up audit of
  the gcd recovery, then rebase and rerun the conformance fixture and PARI
  profile.

## Blockers

- None.
