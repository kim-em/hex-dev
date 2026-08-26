# Steered unified-dispatch evidence refresh (PR #6822)

## Accomplished

- Ran the post-#6809 steered evidence refresh the worker left out of scope:
  re-swept both consolidated steered families on carica at 30d02fca,
  repointed the comparator script, regenerated both figures, recomputed the
  scaling + performance report blocks/prose. PR #6822 (branch
  steered-unify-evidence-refresh), wait-for-ci + squash-merge chained.
- Headline: random-bounded n=30 dispatched 14.27 -> 4.44 ms; the bottom
  elbow is gone, curve monotone with one ~n^3.5 slope across 30..180.
  The fix answers Kim's original question — n=30 now continues smoothly
  down because it routes to steered instead of falling back to exact.
- Contention caught and handled: the first random-bounded pass corrupted
  the load-sensitive Isabelle external comparator (R^2 0.82, +40%); re-ran
  once, Isabelle native back to R^2 0.998. Did NOT commit the contaminated
  curve. (Confirmed this session runs ON carica, so host load is shared
  with pod agents.)
- Scratch: SteeredProbe.lean (untracked, repo root) — the n=30 diagnostic.

## Current frontier

PR #6822 in CI. On merge, the committed figures match the shipped unified
dispatch and the LLL elbow program is complete: all three comparator
elbows Kim raised are resolved (n=25 certified = measured optimum doc'd;
harsh-cubic n=35/40 steered = fixed by two-tier then unified; random-bounded
n=30 steered = fixed by drift margin + unification).

## Next step

Confirm #6822 merges green.

## Blockers

None.
