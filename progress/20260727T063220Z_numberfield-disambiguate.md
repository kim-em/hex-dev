# HexNumberField bounded disambiguation

## Accomplished

- Added evaluation-eliminant normalization by maximal `X`-factor removal and
  primitive-part normalization.
- Added the reciprocal-Cauchy lower-bound denominator and conservative
  fixed-field coordinate/Horner error majorants.
- Implemented the SPEC's finite disambiguation endpoint and least-precision
  search using exact dyadic radius comparisons.
- Added a checked candidate decision that retains zero eliminants immediately
  and otherwise excludes candidates only with a certified nonzero ball.
- Added compiled normalization, endpoint, least-precision, and zero-eliminant
  regressions and rebuilt the umbrella `HexNumberField` target.

## Current frontier

The bounded candidate-selection substrate shared by fixed-field roots and
tower adjoining is executable. The later root driver must construct each
candidate evaluation eliminant and supply its certified ball evaluator.

## Next step

Publish this milestone, start its review monitor, then repair the completed
minimal-polynomial review findings and propagate the stacked branches before
starting `AlgebraicPoly` and the root driver.

## Blockers

None.
