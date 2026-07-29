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
Phi_385 cases to their prior performance. The clean full-corpus Hex-only sweep
solves 373/392 with a 432.972 microsecond median and 5.437 millisecond p90. On
238 overhead-eligible pairs its median Hex/Isabelle ratio is 0.927x, with Hex
winning 126 rows and Isabelle 112.
The affected quadratic-multifactor benchmark remains flat at the largest rung:
67.229 ms versus the preceding 67.862 ms.
The five affected parametric BZ registrations were also refreshed; the public
degree-24 rung is 1.786 ms.
The five affected fixed BZ registrations pass their expected-hash checks; their
medians are 31.525 microseconds (`X^4 + 1`), 29.363 microseconds (paired
quadratics), 91.796 microseconds (`Phi_15`), 1.583 ms (`SD_3` lattice), and
29.299 ms (`SD_4` lattice).
All current performance reports now point at the clean guarded-tree sweep and
affected overlays. All 25 cross-system figures were regenerated; their
provenance output selects the new Hex artifact and the unchanged current
PARI, NTL, FLINT, and Isabelle artifacts.
- An independent second opinion found no blocking correctness or soundness
  issue. Follow-up cleanup makes prefix-order dependence and deliberate
  opacity explicit, computes relift split data only on eligible nodes, folds
  degree statistics once, hardens the diagnostic's fuel/path handling, and
  documents the relift guard in the BZ SPEC.
- Fresh BZ fixture emission matches the committed fixture; the FLINT oracle
  checks all 102 cases and the trace gate checks all 52 traces with zero
  failures.

## Next step

Refresh the now-stale isolated Hex lattice and classical corpus services (but
not the unchanged external comparators), regenerate merged figures and paired
statistics, then publish and merge this intermediate PR. Continue from the
remaining Chebyshev/Legendre and Swinnerton-Dyer gaps afterward.

## Blockers

None.
