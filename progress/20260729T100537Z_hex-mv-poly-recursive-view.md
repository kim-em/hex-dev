# Hex multivariate polynomial recursive view

## Accomplished

- Proved the coordinate insertion/removal laws and injectivity of
  `insertVar`.
- Refactored `toUnivariate` into named, proof-friendly two-pass array
  helpers while preserving its sparse executable behavior.
- Switched bucket updates from singleton-polynomial allocation plus merge to
  the direct `addMonomial` tree update.
- Proved both coefficient characterizations and both
  `toUnivariate`/`ofUnivariate` round trips.
- Removed the unused `IsMonomialOrder` requirement from the recursive view,
  retaining only the comparator laws actually needed by storage, and updated
  the SPEC accordingly.
- Added kernel round-trip coverage for first, last, and middle variables,
  sparse dense coefficients with an interior zero, the zero polynomial, and
  the one-variable boundary.
- Ran focused builds and the full 9,631-target `lake build`. Axiom audits of
  the four generic theorems and six concrete kernel tests contain no
  `sorryAx`; `#guard_msgs` makes the concrete test audit CI-enforced.
- Obtained two independent Claude review passes, addressed their pre-merge
  issues and several concrete performance, documentation, naming, and
  coverage suggestions.

## Current frontier

Five `HexMvPoly` sorries remain: the three `IsMonomialOrder` instances in
`Mono.lean`, `coeff_pow_succ` in `Operations.lean`, and
`partialEval_eq_subst` in `Structural.lean`.

## Next step

Land the recursive-view checkpoint after the Horner PR merges, then prove the
operation and structural laws before tackling the three well-founded
monomial-order instances.

## Blockers

No implementation blocker. The preceding Horner PR is still running CI, so
this checkpoint has not yet been opened as a second concurrent PR.
