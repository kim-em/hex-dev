# Steered-dispatch recalibration and packed-gate removal directives

## Accomplished

- Confirmed Kim's two figure observations from the committed steered
  exports: harsh-cubic dispatched curve is non-monotone (20.71 ms @35 >
  16.33 ms @40 — n=35 misrouted to exact, steered ~11 ms) and the
  random-bounded 30->45 segment is near-flat (15.30 -> 17.75, steered at
  30 extrapolates to ~4-5 ms, ~3x misrouted). Both are the dimension-only
  steerDimThreshold (n < 40) failing per family, the reducer-side analogue
  of #6757's checker-predictor entanglement.
- Filed https://github.com/kim-em/hex/issues/6781 (recalibrate the
  steered-reducer dispatch boundary per family): probe + paired gates
  (HC n=35 >= 1.5x, RB n=30 >= 2x, monotone family curves, no rung
  regresses, bz-recombination unchanged — non-negotiable), no SPEC change
  needed (SPEC's dispatch sentence is permissive).
- Filed https://github.com/kim-em/hex/issues/6782 (remove the packed
  word-scale regime gate) per Kim's uniformity preference, with the
  explicitly blessed relaxed gate (sub-10 ms rungs may regress <= 10% and
  <= 1 ms; >= 10 ms rungs within 3%). SPEC PR required first — the regime
  gate is currently mandated in §Certified external dispatch. Labelled
  blocked: same bench host as 6781's sweep; serialize.
- Fired 6781 via wt (~/worktrees/hex/hex-issue-6781).

## Current frontier

#6781 in flight; #6782 queued behind its carica sweep.

## Next step

When 6781's measurement is done (or the issue resolves), fire wt 6782.

## Blockers

Carica serialization between 6781 and 6782.
