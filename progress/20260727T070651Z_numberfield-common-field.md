# HexNumberField common-field roots

## Accomplished

- Added a deterministic bounded primitive-element search for arrays of
  canonical algebraic coefficients, choosing a maximal-degree shift so field
  overlaps do not invalidate the degree target.
- Added exact rational, sum, product, scale, power, and field-trace helpers.
- Recovered fixed-field coordinates with the nondegenerate trace pairing and
  validated every recovered coordinate by canonical algebraic equality.
- Added `AlgebraicPoly.roots?` and `AlgebraicPoly.roots`, delegating to the
  fixed-field root driver after common-field conversion.
- Added compiled end-to-end checks for `T - sqrt 2`, the zero polynomial, and
  a nonzero constant polynomial.
- Built the complete repository successfully.

## Current frontier

The Mathlib-free root API now covers both fixed presentations and arbitrary
canonical algebraic coefficient arrays. An asynchronous review of the prior
`AlgebraicPoly` representation identified that constructor privacy alone does
not carry its normalization invariant into proofs quantified over all values.

## Next step

Add an erased normalization proof to `AlgebraicPoly`, rebase this common-field
milestone over that repair, then begin the tower implementation.

## Blockers

None.
