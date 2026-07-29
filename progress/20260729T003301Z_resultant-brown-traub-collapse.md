# Resultant Brown--Traub degree collapse

## Accomplished

- Proved sparse-first-row determinant expansion for the local determinant.
- Proved one-step and iterated retained-formal-degree collapse for generalized
  Sylvester minors.
- Proved the right-degree edge law, the full Brown--Traub factorization, and
  its endpoint polynomial identity.
- Derived the executable exact scalar quotient from the endpoint identity in
  every nontrivial exact-division coefficient ring.
- Added discriminating endpoint and interior-index conformance guards and
  updated the Resultant SPEC and manual chapter.
- Ran a fresh independent mathematical review, targeted builds, and the full
  9,573-job `lake build` successfully.

## Current frontier

The formal-degree collapse and leading-coefficient factors are now available
as reusable public lemmas. `subresultantOrdered_brownLaw` remains the principal
Resultant proof obligation.

## Next step

Specialize the transformation laws to ordered pseudo-remainders, compose the
nonunit multiple of the left input with `poly_scale_left`, cover the defective
index range, and align the accumulated recursive scalar factors.

## Blockers

None.
