# Polynomial GCD and Hensel kernels

## Accomplished

- Added a proof-backed remainder-only dense-polynomial division loop and used
  it for compiled Euclidean GCD, avoiding quotient allocation when every
  quotient is discarded.
- Added exact inverse-cached finite-field remainder/GCD workers and routed
  Berlekamp splitting and BZ good-prime screening through them.
- Replaced list/range round trips in integer-to-finite-field and prime-power
  coefficient reduction with proved array-map implementations, hoisting the
  prime-power modulus out of the coefficient loop.
- Replaced generic schoolbook multiplication by a monomial in quadratic
  Hensel division with an exactly equal shift-and-scale kernel.
- Completed the 9,636-job full build and the polynomial (103), finite-field
  (8), Berlekamp (47), Hensel (69), and BZ (16) executable verification suites.
- Recorded clean, CPU-pinned 392-row public, lattice, and classical-no-decline
  artifacts from commit `09f7f532`. Public Hex retains 373 solves and measures
  0.881x median Hex/Isabelle BZ over the 236 current overhead-eligible rows;
  it wins 138 of those comparisons. The Chebyshev and Legendre family medians
  are now 1.68x and 1.55x, and the degree-240 cyclotomic probe is 451 ms.
- Confirmed that the apparent classical advantage was diagnostic overhead,
  not an algorithmic lead: public/classical is 1.001x median over 241 eligible
  rows (119 public wins, 122 classical), while public retains the additional
  `sd6` solve and its bounded-decline, fallback, and result-checking behavior.
- Regenerated the complete factor-sweep figure set from the new Hex artifacts
  without rerunning the current FLINT, PARI, NTL, or Isabelle measurements.
- Refreshed the eight non-scheduled parametric BZ benchmark series on CPU 0;
  every row passed its checksum and the export records a clean tree.

## Current frontier

The shared GCD and Hensel kernels are fully proof-backed and validated, and the
clean current corpus artifacts are ready to publish. Swinnerton-Dyer degree 32
remains about 4--5x slower than Isabelle and is dominated by recombination
rather than the improved lifting path.

## Next step

Refresh the lower-layer BZ benchmark exports and aggregate reports, publish the
reviewed intermediate PR, and profile the remaining SD5 recombination gap while
CI runs.

## Blockers

None.
