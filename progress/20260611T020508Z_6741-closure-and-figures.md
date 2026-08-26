# #6741 closure bookkeeping and before/after comparator figures

## Accomplished

- Closed https://github.com/kim-em/hex/issues/6741 (packed same-lattice
  certificate) as completed, with a closing comment linking #6745 (SPEC,
  merged first), #6746 (implementation with the word-scale regime gate),
  and #6750 (carica evidence refresh). Final committed effect:
  Lean-certified random-bounded C₃ 197 → 169 ns·n³ (4.4× → 3.8× fpLLL),
  checker rungs -15–20% at n=45–180, harsh-cubic within noise via the gate.
- Posted a baseline note on https://github.com/kim-em/hex/issues/6742:
  measurement protocol unaffected (fresh merge-base baselines); the
  remaining checker headroom is now even more concentrated in the
  reducedness clause; harsh-cubic motivation numbers unchanged.
- Built a before/after view of the comparator figures for Kim:
  /tmp/hexlll-figs/{before,after}/ + comparator-before-after-6741.md
  (opened in VSCode; markdown preview renders the SVGs side by side).
  Finding: only the random-bounded figure changes (Lean-certified curve
  drops); harsh-cubic is byte-identical (no certified curves plotted there
  since #6737, and the regime gate keeps harsh-cubic on the materialized
  comparison). Note: the committed figures at HEAD still predate #6741;
  regenerating them against hex-lll-certified-443bf8fb.json (and possibly
  updating the script default) is an open follow-up.

## Current frontier

#6742 is the open critical-path directive; #6743/#6744 remain blocked on it.

## Next step

A worker claims #6742. Consider a small PR repointing
scripts/plots/hex-lll-comparator.py's DEFAULT_CERTIFIED at the refreshed
export and recommitting the random-bounded figure.

## Blockers

None.
