# Fast polynomial arithmetic research

## Accomplished

- Read `SPEC/future-work.md` from freshly fetched `origin/main` at
  `4a74b7a6ed84fe2ef0a0ad4e386f65a72fee03b4`, specifically the fast
  polynomial arithmetic sketch and its dependency placement.
- Audited the related default-branch implementation and design state:
  generic schoolbook `DensePoly.mul`, schoolbook Euclidean division/gcd,
  the specified but unimplemented `hex-truncated-series`, optional packed
  `FpPoly.mulPacked`, and the proved, measured `ZPoly.mulKronecker` kernel.
- Reviewed the evidence from issues #9142/#9147 and #9320: Karatsuba lost
  to Kronecker on the measured bignum Hensel shapes; single-point Kronecker
  has degree/bit-width cutoffs; truncated series currently has a SPEC only.
- Surveyed David Harvey's primary publication pages and papers on
  multipoint Kronecker substitution, redundant-representation NTT
  butterflies, middle products, truncated/cache-friendly/in-place Fourier
  transforms, fast power-series operations, characteristic-two transforms,
  and asymptotically fast finite-field multiplication.

## Current frontier

- The most actionable Harvey-derived experiments are a two-/four-point
  extension of `ZPoly.mulKronecker` and a raw-word NTT plan using redundant
  residues under the existing `ZMod64` bound.
- The architectural prerequisite for fast division remains implementing
  `hex-truncated-series`, then adding the `DensePoly` reversal/conversion
  bridge in `hex-poly-fast`.
- Low, high, middle, cyclic, and negacyclic products should be treated as
  first-class kernels rather than deriving every consumer from a full
  product.

## Next step

- If this direction is promoted from research to implementation, write a
  `hex-poly-fast` SPEC that separates generic ring Karatsuba, finite-field
  NTT, and integer Kronecker/CRT dispatch, and begin with benchmark-only
  prototypes for multipoint Kronecker and the redundant-residue NTT
  butterfly.

## Blockers

- `hex-truncated-series` is specified but not implemented or registered in
  `libraries.yml`; fast reciprocal/division cannot yet consume it.
- No current large-degree workload establishes a need for the much more
  elaborate Harvey--van der Hoeven asymptotic finite-field algorithms.
