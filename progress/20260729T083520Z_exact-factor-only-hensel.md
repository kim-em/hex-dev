# Exact-exponent, factor-only Hensel lifting

## Accomplished

- Replaced next-power-of-two Hensel lifting with a verified exact-target
  recursion through `ceil(k / 2)`, limiting transient overshoot to one
  exponent for odd targets.
- Added word and bignum factor-only final corrections, proved them equal to
  projecting the full quadratic step, and moved the balanced production lift
  to that surface without weakening the executable or Mathlib contracts.
- Refreshed every affected Hex measurement while retaining the already-current
  FLINT, PARI/GP, NTL, and Isabelle exports. The public corpus result remains
  373/392 with a 424.039 µs median and 5.577 ms p90; on 238 eligible Isabelle
  pairs the median ratio is 0.930x and Hex wins 126/112.
- Retained the exact-only A/B, refreshed the changed Hensel and BZ benchmark
  registrations, updated the production/full-witness diagnostic, and
  regenerated all 25 cross-system figures.
- Incorporated an independent review's SPEC, provenance, attribution, and
  documentation findings. The final state passes the 9,629-job `lake build`,
  focused benchmark verification, release/trust/DAG/source checks,
  Mathlib-free bench lint, conformance-matrix validation, and 110 script tests.

## Current frontier

Public factorization is no longer systematically slower than the isolated
classical route: their eligible-row median is 0.996x and public wins 126/112.
The aggregate public/Isabelle ratio is now 0.930x, but Chebyshev and Legendre
remain above 2x at their family medians and the per-row tail is still broad.

## Next step

Publish and merge this evidence-backed intermediate PR. Then profile the
Chebyshev and Legendre losses, starting with degree-balanced split-tree shape
and multiword polynomial arithmetic, and measure the smallest general verified
improvement against the retained corpus.

## Blockers

None.
