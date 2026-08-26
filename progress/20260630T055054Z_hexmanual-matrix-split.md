# HexManual matrix-chapter split (PR 1 of the manual refresh)

## Accomplished

- Split the single `HexManual/Chapters/HexMatrix.lean` chapter, which
  conflated four now-separate libraries, into four per-library chapters:
  - `HexMatrix.lean` trimmed to the dense-matrix core.
  - new `HexDeterminant.lean`, widened toward its README (Laplace
    `det_eq_foldl_laplace_row`, `det_setCol_add`, `adjugate`/
    `mul_adjugate`, Cauchy-Binet, Plücker, triangular).
  - new `HexRowReduce.lean` (Gauss-Jordan, span, nullspace).
  - new `HexBareiss.lean` (fraction-free integer determinant).
- Fixed stale prose: the core chapter claimed the identity is exposed
  via a `One` instance, but that instance was dropped from the
  Mathlib-free core and now lives only in `HexMatrixMathlib`.
- Registered all four chapters in `HexManual.lean` (dependency order)
  and cross-linked them with `{ref}` tags.
- `lake build HexManual` green in a fresh clone: every `{docstring}`
  resolves, every worked-example `#guard` passes, no over-length code
  lines, no warnings on the four chapters.

## Current frontier

PR 1 is committed on `claude/manual-matrix-split`. PR 2 (per-chapter
`# Recipes` how-to sections, mathlib-phrasebook style) starts with a
single exemplar recipe for review before the rest are written.

## Next step

Land the exemplar recipe (kernel basis, HexRowReduce) for review, then
the first-pass recipe set (matrix family + HexGF2/HexGFq/HexLLL). Then
PR 3: `PLAN/Phase7.md` one-chapter-per-library rule + `SPEC/recipes.md`.

## Blockers

None. README quickstarts (HexMatrix/HexDeterminant) still use
`(1 : Matrix ...)` for the identity, which no longer elaborates after
the `One`-instance drop; that is released-README source, out of scope
for the manual PRs but worth a separate fix.
