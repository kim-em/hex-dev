# LLL performance: four directives filed

## Accomplished

Filed the four LLL-performance directives designed in the previous session
(see progress/20260610T075718Z_lll-performance-ideas.md for the measurement
basis). Each issue carries a paired before/after measurement protocol on the
existing bench ladders, explicit go/no-go thresholds, and the instruction not
to open or merge the PR if the hoped-for improvement is not realised:

- https://github.com/kim-em/hex/issues/6741 (HexLLL: replace sameLatticeCert
  matmul equalities with packed single-point evaluation) — claimable now.
- https://github.com/kim-em/hex/issues/6742 (HexLLL: fixed-precision interval
  reducedness checker with exact fallback) — claimable now; the flagship
  (harsh-cubic certified exponent fix).
- https://github.com/kim-em/hex/issues/6743 (HexLLL: request stronger
  (delta, eta) from fplll than certCheck certifies) — labelled blocked on
  #6742.
- https://github.com/kim-em/hex/issues/6744 (HexLLL: approximation-steered
  native reducer with certified output) — labelled blocked, recommended
  after #6742.

## Current frontier

Issues are live; no implementation started. #6741 and #6742 are independent
and can be claimed in parallel.

## Next step

Workers claim #6741 / #6742. After #6742 merges, unblock #6743 and #6744.

## Blockers

None.
