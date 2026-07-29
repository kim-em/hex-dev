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
- On the 392-row development sweep, public Hex retained 373 solves and moved
  from 0.909x to 0.887x median Hex/Isabelle BZ over the same 238
  overhead-eligible rows. The Chebyshev and Legendre family medians moved from
  2.05x and 1.85x to 1.93x and 1.71x; the degree-240 cyclotomic probe dropped
  from about 905 ms to 505 ms.
- After hoisting the modulus, focused clean runs moved the Chebyshev and
  Legendre family medians further to 1.66x and 1.50x versus Isabelle; their
  paired medians versus the merged Hex artifact are 0.887x and 0.869x. The
  degree-240 cyclotomic probe dropped again to about 462 ms.

## Current frontier

The shared GCD and Hensel kernels are fully proof-backed and validated. The
development sweep was run from the pre-rebase worktree and is evidence for the
change, not yet the final committed report artifact; the focused family runs
were taken after the clean rebase. Swinnerton-Dyer degree 32
remains about 4x slower than Isabelle and is dominated by recombination rather
than the improved lifting path.

## Next step

Rebase onto merged `main`, take an independent review, publish the intermediate
PR, and while CI runs profile the remaining SD5 recombination gap.

## Blockers

None.
