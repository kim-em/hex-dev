# HexNumberField fixed-field approximation

## Accomplished

- Added explicit dyadic complex-ball zero, addition, multiplication, and
  rational enclosure operations.
- Added Horner evaluation of rational coordinate polynomials on a dyadic root
  square, together with input-derived coefficient and Cauchy guard-bit bounds.
- Implemented `QAdjoin.approx` as a single threaded refinement followed by
  canonical-coordinate ball evaluation, with a sound checked fallback.
- Added compiled guards for exact complex-ball arithmetic, non-dyadic rational
  rounding, and linear Horner evaluation.
- Rebuilt `HexNumberField` and reran DAG, source, phase, bench-import,
  conformance-matrix, forbidden-form, and whitespace checks successfully.

## Current frontier

The fixed-field representation, canonical reduced arithmetic, inversion, and
threaded approximation layers are implemented.  The companion proof that the
approximation radius reaches the requested precision remains a later Mathlib
obligation.

## Next step

Publish the stacked approximation PR and launch its independent review, then
repair the already-returned resultant and number-field scaffold review findings
while that review and CI continue asynchronously.

## Blockers

The repository phase scheduler still blocks HexNumberField Phase 1 on
HexBerlekampZassenhaus reaching Phase 1, although the dependency APIs used here
are present and compile.
