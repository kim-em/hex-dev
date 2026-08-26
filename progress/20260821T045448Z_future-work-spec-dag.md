# Future-work SPEC dependency DAG

## Accomplished

- Updated `SPEC/future-work.md` against `origin/main` to remove the completed
  Desnanot-Jacobi item and describe the remaining determinant work as a
  dependency of generic Bareiss rather than a new library.
- Added the shared exact-division refactor and assigned generic Bareiss to the
  existing `hex-bareiss` library.
- Named and separated the proposed characteristic-polynomial,
  minimal-polynomial, polynomial-Smith, invariant-factor, sparse-polynomial,
  truncated-series, cyclotomic, multivariate-Hensel, multivariate-factor, and
  fixed-precision p-adic library pairs.
- Recorded hard dependencies, deliberately absent dependencies, and the
  decision to defer a swappable-polynomial typeclass abstraction.

## Current frontier

- The documentation-only branch is ready for review and an upstream PR.
- Independent SPEC/refactor jobs can be dispatched in dependency waves from
  the boundaries recorded in `SPEC/future-work.md`.

## Next step

- Review and merge the future-work PR, then dispatch the shared exact-division,
  determinant API audit, and independent leaf SPEC jobs. Dispatch generic
  Bareiss, invariant factors, multivariate factorization, and consumer adapters
  only after their stated prerequisite jobs land.

## Blockers

- None.
