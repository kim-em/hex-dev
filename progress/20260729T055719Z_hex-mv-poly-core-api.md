# Hex multivariate polynomial core API

## Accomplished

- Registered the Mathlib-free `HexMvPoly` library and the planned
  `HexMvPolyMathlib` companion in the dependency manifest.
- Implemented the executable `Mono` and canonical `MvPoly` data paths:
  monomial operations and orders, normalized constructors, sparse arithmetic,
  degree and leading-term queries, direct and Horner evaluation, collision-safe
  structural transformations, and the recursive `DensePoly` view.
- Added the public SOS/CompPoly compatibility spellings (`toList`,
  `leadingMonomial`, `bind`, `bind₁`, and `sumToIter`) after checking the pinned
  downstream sources.
- Added downstream `decide +kernel` checks over both `Int` and `Rat`, including
  arithmetic, evaluation, and a computed recursive-view round trip.
- Opened issue #9074 as the end-to-end implementation tracker.

## Current frontier

The executable core API is present with its final intended signatures and
builds through `HexMvPoly.KernelTests`. The coefficient, order, invariant, and
round-trip theorem statements are present but still contain 37 explicit
`sorry` placeholders, as allowed for the API-stub milestone.

Documentation PR #9073 is still running CI and is undergoing the requested
independent Claude review. The implementation commit is being kept local until
that documentation PR merges.

## Next step

Land the reviewed documentation PR, rebase this implementation onto `main`,
and open the core API milestone PR. Then discharge the core theorem
placeholders while beginning the Mathlib companion and its SOS/CompPoly compile
acceptance modules.

## Blockers

None. The only sequencing constraint is to avoid pushing implementation commits
onto the documentation-only PR branch.
