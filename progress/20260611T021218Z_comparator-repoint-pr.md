# Comparator export repoint PR

## Accomplished

Opened https://github.com/kim-em/hex/pull/6751 (doc: repoint comparator
plots at the refreshed Lean-certified export), branch
`comparator-certified-export-refresh`. It fixes two staleness issues left
by #6750: the committed random-bounded comparator figure predated #6741,
and `scripts/plots/hex-lll-scaling.py --all` did not reproduce the
committed scaling table (the script reads the comparator's FAMILIES
defaults, which still pointed at `hex-lll-certified-carica.json`).
Changes: `DEFAULT_CERTIFIED` → `hex-lll-certified-443bf8fb.json` with the
Isabelle-certified series kept on the carica export (no Isabelle rows in
the refreshed one), regenerated random-bounded SVG (harsh-cubic
regenerates byte-identically), and the scaling report's random-bounded
block replaced with the exact regenerated output — note the committed
C₃ 169 was not reproducible; the committed export yields 171. Caveats
section now names all three runs.

## Current frontier

PR awaiting review/merge. #6742 remains the open critical-path directive.

## Next step

Merge #6751 when CI is green; workers claim #6742.

## Blockers

None.
