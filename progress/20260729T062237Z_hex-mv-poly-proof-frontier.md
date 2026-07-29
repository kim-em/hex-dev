# Hex multivariate polynomial proof frontier

## Accomplished

- Proved the four divisibility laws relating componentwise monomial gcd and
  lcm.
- Reimplemented `restrictBy` as a direct `ExtTreeMap.filter`, reduced its
  bounds to `[Zero R]`, and proved both preservation of the nonzero invariant
  and `coeff_restrictBy`.
- Closed `coeff_homogeneousComponent`, `eval₂_eq`, and `eval_eq`.
- Rebuilt the affected modules and the downstream kernel replay tests
  successfully.

## Current frontier

The canonical core compiles and its kernel tests pass. Twenty-three theorem
obligations remain: seven monomial/order laws, five coefficient arithmetic
laws, two Horner equivalences, five structural laws, and four recursive-view
laws.

## Next step

Land the reviewed SPEC follow-up, rebase the core branch onto it, and publish
the API/core proof milestone. Then close the remaining coefficient laws before
building conformance and benchmark surfaces.

## Blockers

None.
