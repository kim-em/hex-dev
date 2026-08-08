# Hex multivariate polynomial multiplication coefficient law

## Accomplished

- Proved `coeff_mul` for arbitrary `Lean.Grind.Semiring` coefficients.
- Connected the executable Gustavson traversal to its flattened list of
  stored term pairs, then to the canonical support-pair enumeration.
- Proved the active support pairs are a permutation of the supported entries
  in `Mono.splits`, using split uniqueness and support-list uniqueness.
- Added reusable support/lookup lemmas to `MvPoly.Basic`.
- Generalized additive-only `HexBasic.Fold` lemmas from ring hypotheses to
  semiring hypotheses, matching the algebra they actually use.
- Rebuilt kernel tests and passed DAG, release-manifest, trust-surface, and
  Phase 4 checks.

## Current frontier

- The core implementation now has ten remaining proof obligations; the
  multiplication convolution is no longer one of them.
- The follow-up branch contains the reusable tree-map API, addition
  integration, split uniqueness, and multiplication coefficient proof, all
  rebased onto current `main`.

## Next step

- Obtain an independent review of this follow-up and open its intermediate PR.
- While that PR runs, continue with the power recurrence or another independent
  correctness obligation on a branch based on the follow-up head.

## Blockers

- None.
