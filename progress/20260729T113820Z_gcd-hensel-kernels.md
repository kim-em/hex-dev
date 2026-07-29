# Polynomial GCD and Hensel kernels

## Accomplished

- Added a proof-backed remainder-only dense-polynomial division loop and used
  it for compiled Euclidean GCD, avoiding quotient allocation when every
  quotient is discarded.
- Added exact inverse-cached finite-field remainder/GCD workers and routed
  Berlekamp splitting and BZ good-prime screening through them.
- Replaced list/range round trips in prime-power coefficient reduction with a
  proved array-map implementation, hoisting the modulus out of the coefficient
  loop. Retained the exact array-map theorem for ordinary `modP` without using
  it as the compiled implementation after the A/B below.
- Replaced generic schoolbook multiplication by a monomial in quadratic
  Hensel division with an exactly equal shift-and-scale kernel.
- Completed the post-merge 9,634-job full build and the polynomial (103), finite-field
  (8), Berlekamp (47), Hensel (69), and BZ (16) executable verification suites.
- Recorded a definitive clean, CPU-pinned 392-row artifact from commit
  `0b95505b` covering public, lattice, and classical-no-decline together.
  Public Hex retains 373 solves and measures 0.887x median Hex/Isabelle BZ over
  234 current overhead-eligible rows; it wins 135 of those comparisons. On the
  preceding fixed 238-row eligibility set the ratio is 0.870x. The Chebyshev
  and Legendre family medians are now 1.64x and 1.49x, and the degree-240
  cyclotomic probe is 447 ms.
- Confirmed that the apparent classical advantage was diagnostic overhead,
  not an algorithmic lead: public/classical is 1.006x median over 237 eligible
  rows (109 public wins, 128 classical), while public retains the additional
  `sd6` solve and its bounded-decline, fallback, and result-checking behavior.
- Regenerated the complete factor-sweep figure set from the new Hex artifacts
  without rerunning the current FLINT, PARI, NTL, or Isabelle measurements.
- Refreshed the complete HexPolyFp (8), Berlekamp (4), Hensel (9), and
  non-scheduled BZ parametric (8) and fixed (8) measurement sets on CPU 0;
  every row passed its checksum and every final export records a clean tree.
- The complete lower-layer refresh exposed a 1.63x `modP` regression from the
  direct `Array.map` implementation. A same-code A/B measured 15.194 ms with
  the replacement and 9.677 ms through the reference compiled path, so the
  `csimp` rule was removed while retaining its equality theorem. The separate
  `reduceModPow` array kernel remains enabled and improves its largest rung
  from 10.276 ms to 0.733 ms.

## Current frontier

The shared GCD and Hensel kernels are fully proof-backed and validated, and the
clean current corpus and lower-layer artifacts are ready to publish. Against
the immediately preceding public export, the all-row paired median is 0.964x
and current Hex wins 306 of 373 rows. Swinnerton-Dyer degree 32 remains about
4--5x slower than Isabelle and is dominated by recombination rather than the
improved lifting path.

## Next step

Validate the final reports/artifacts, publish the independently reviewed PR,
and profile the remaining SD5 recombination gap while CI runs.

## Blockers

None.
