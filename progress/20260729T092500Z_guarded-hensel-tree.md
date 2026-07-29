# Guarded multifactor Hensel tree

## Accomplished

- Confirmed that exact-factor PR #9083 passed its single CI job and merged as
  `716a0d49`.
- Rebased the follow-up optimization branch onto that merged `main`.
- Added a conservative degree-aware multifactor Hensel split: retain the
  count-halving tree normally, but balance total degree when one modular factor
  exceeds half the node degree.
- Restricted the deeper recursive relift ladder to four-factor nodes with
  precision above 300.
- Extended the prime-policy diagnostic to A/B the old count tree against the
  production tree and to load named outliers from the committed corpus.
- Verified the full `HexBerlekampZassenhausMathlib` target (9,102 jobs).

## Current frontier

Targeted measurements retain the large Chebyshev U24, Legendre P30/P38, and
Conway improvements while restoring the regressing P16, P24, P26, P28, and
Phi_385 cases to their prior performance. The final full-corpus Hex-only sweep
has not yet been recorded.

## Next step

Commit the exact implementation revision, run one replacement Hex-only corpus
sweep on CPU 0, then regenerate the affected reports and figures without
rerunning the current PARI, NTL, FLINT, or Isabelle comparators.

## Blockers

None.
