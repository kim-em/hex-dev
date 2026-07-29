# Hex multivariate polynomial split uniqueness

## Accomplished

- Proved `Mono.dropHead_prepend`, the inverse needed to reason about the
  recursive split encoding.
- Proved `Mono.splits_nodup` by showing each recursive block is injective and
  different head-exponent blocks are disjoint.
- Confirmed the initial core API PR passed its full CI pipeline and
  auto-merged.

## Current frontier

- `Mono.splits` now characterizes every factorization and enumerates each one
  exactly once.
- The follow-up tree-map work is ready to rebase onto the squash-merged core.
- The remaining multiplication coefficient proof can now use permutation and
  single-indicator fold arguments soundly.

## Next step

- Rebase the follow-up branch onto current `main`.
- Finish `coeff_mul`, using the new split uniqueness theorem and reusable
  additive fold algebra.

## Blockers

- None.
