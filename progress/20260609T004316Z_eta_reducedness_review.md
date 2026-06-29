# Eta-reduced LLL design review

## Accomplished

Reviewed the proposed `eta = 11/20` reducedness revision for certified fpLLL
output against the current HexLLL and BZ specs. Checked the existing strict
`1/2` LLL theorem surface, the short-vector proof chain, integer
`scaledCoeffs` representation, and BZ's use of LLL short-vector output.

## Current frontier

The revision is mathematically plausible but changes public theorem constants
and preconditions. The largest risks are downstream consumers relying on the
classical `delta = 3/4`, `alpha = 2` bound, and any claim that fpLLL's floating
point `eta = 0.51` gives a rigorous exact-rational `eta = 0.55` guarantee.

## Next step

If this design is adopted, specify separate public theorem names for classical
`eta = 1/2` and certified-fpLLL `eta = 11/20`, and require the checker
soundness theorem to be the only trusted bridge from external candidates to
LLL reducedness.

## Blockers

None for the review. No implementation was attempted.
