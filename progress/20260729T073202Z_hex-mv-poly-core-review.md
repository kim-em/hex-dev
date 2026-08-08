# Hex multivariate polynomial core review

## Accomplished

- Opened intermediate core PR #9077 and obtained an independent review of its
  exact diff.
- Corrected the Horner equality bounds to commutative semirings after verifying
  the noncommutative counterexample.
- Separated `TransCmp` and `LawfulEqCmp` instances for lex, grlex, and grevlex
  from the remaining `IsMonomialOrder` proofs.
- Made addition fold the smaller support into the larger support.
- Expanded downstream kernel probes across power, `BEq`, coefficients, monomial
  arithmetic, all three named comparators, and arities zero through two.
- Aligned the computational benchmark-family registry with the SPEC, listed
  `HexMvPoly` explicitly in CI, removed redundant recursive-view instance
  binders, and proved `sumToIter_eq`.

## Current frontier

- PR #9077 needs an independent re-review of the amended head and CI.
- The core still has 11 explicitly reserved proof obligations.
- Reusable tree-map algorithms currently live in `Std`; the next implementation
  checkpoint will add a designated Hex extension module for missing generic
  operations and make `MvPoly` consume it.

## Next step

- Push the review fixes, update the PR description, and re-run the independent
  review.
- Begin the reusable `ExtTreeMap` API with a size-biased, deletion-capable
  collision merge and its lookup laws before further polynomial arithmetic
  optimization.

## Blockers

- None.
