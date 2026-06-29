# Steered robustness directive filed and fired

## Accomplished

- Filed https://github.com/kim-em/hex/issues/6806 (HexLLL: fix
  steered-reducer float drift and unify the dispatch threshold) from the
  n=30 investigation. Two coupled deliverables that must land together:
  (1) tighten δsteer to (δ+3)/4 to fix the missed-swap drift bug;
  (2) collapse steerWins from the two-tier operand-width split to a single
  n≥30 threshold, removing steerWideDimThreshold/steerBitThreshold/the
  maxDiagBits branch. Gates: n=30 elbow gone, case-splitting reduced,
  zero fallbacks across both ladders + seeds 1..12, bz unchanged
  (non-negotiable), no rung regresses. SPEC-neutral.
- Fired via wt: ~/worktrees/hex/hex-issue-6806.

## Current frontier

#6806 in flight — the last LLL figure/uniformity item. Probe evidence in
SteeredProbe.lean (untracked).

## Next step

Monitor #6806; on merge it removes the random-bounded steered elbow and
the operand-width dispatch case-split.

## Blockers

Carica contention — directive instructs a load check before measuring.
