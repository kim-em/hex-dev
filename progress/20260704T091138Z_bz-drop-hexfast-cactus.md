# BZ cactus charts: drop the retired hex-fast curve

## Accomplished
Follow-up to the BZ factor-path cleanup: the standalone factorFast tier was
retired (#8589), so the hex-fast comparator no longer exists. Dropped it
from the cross-system cactus/runtime-degree charts:
- Stripped the 391 hex-fast result rows (and the hex-fast entry in
  config.systems) from the baseline sweep record
  reports/bench-results/hexbz-factor-sweep-bc958d84-carica.json; every other
  system's committed measurements are byte-identical (pure deletion, no
  reformatting).
- Removed the hex-fast entry from the STYLE map in
  scripts/plots/hexbz-cactus.py.
- Regenerated the 20 affected SVGs under reports/figures/ via matplotlib
  (Nix). No hex entries were re-measured on this machine (per SPEC, routine
  timings live on dedicated hardware); the surviving hex + external
  comparator curves carry over from the committed baseline unchanged.

Verified by rendering hexbz-cactus-combined.svg to PNG: eight curves (hex
factor/lattice/classical-nodecline + FLINT/NTL/PARI + Isabelle BZ/LLL), no
hex-fast.

## Current frontier
The published charts match the post-cleanup tier set.

## Next step
None.

## Blockers
None.
