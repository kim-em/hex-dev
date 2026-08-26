# Manual + library revision for the matrix-family chapters

## Accomplished

Two stacked PRs off `main`, both building the whole graph green
(computational libs, the five `*Mathlib` bridges, and `HexManual`).

**PR 1 — `matrix-family-lemma-coverage` (#8549), library.**
- Completed the `getElem_`/`row_`/`col_` description-lemma grid in
  `HexMatrix` (zero, identity, mul via `dotProduct`, transpose,
  gramMatrix, principalSubmatrix, and the elementary row ops).
- Added column mirrors `colSwap`, `colScale` with full lemma sets and
  `transpose_colSwap`/`transpose_colScale` bridges.
- Restated `det_colSwap` against `colSwap` (dropping the ugly
  `ofFn`/`finTranspose` form; no downstream callers), added `det_colScale`
  and `det_setRow_add` via `det_transpose` + a new `transpose_setRow`
  bridge.
- Gave `GramSchmidt.Int.gramDet` a `by omega` autoparam on `k ≤ n`.
- Added a `Repr (Vector R n)` instance rendering `#v[...]`.

**PR 2 — `manual-matrix-family-revision`, manual (+ two coupled docstrings).**
- HexMatrix chapter: split "The dense matrix type" into definitions then a
  new "Entry, row, and column lemmas" section asserting total coverage;
  documented `colSwap`/`colScale`; added a `rowAdd` worked example.
- HexRowReduce: dropped the "Build the matrix with the `#m[...]` literal"
  sentence.
- HexDeterminant / HexBareiss: worked examples now use `#m[...]` literals;
  each gained a "The Mathlib correspondence" section (`det_eq`,
  `bareiss_eq_det`/`bareissDet_eq_det`) — added a docstring to
  `HexMatrixMathlib.det_eq` to support it.
- HexGramSchmidt: corrected the false "casts to `Rat` first" framing (the
  Int computable API is exact integer), fixed the "documented by
  signature"/"performance bottleneck" prose, rewrote the worked example
  (`#m` literal, numerals not `i0/i1/i2`, `gramDet` autoparam drops
  `by decide`, whole `scaledCoeffs` matrix printed via `#eval`, size-reduced
  row shown as `#v`), and added a Mathlib correspondence section.
- HexLLL: removed stale/`Internal`-namespace exposition; clarified the
  interval-pass text is checker-side (the steered reducer is gone, the
  checker dispatch is not); fixed the "same-lattice side" slop; dropped
  "overflow-safe"; foreshadowed the native-vs-certified dispatch before
  "one signature"; moved the size-reduction-bound and short-vector
  subsections next to `Hex.lll`; expanded the `Unchecked` discussion;
  rewrote "Certified external dispatch" as a user-facing runtime-switch
  (`HEX_FPLLL_FFI_LIB`) explanation with no `Internal` identifiers; worked
  example uses `#m`/`#v`; added a new minimal-polynomial-recovery example
  (root of `x⁴ − x − 1` from its decimal, via LLL). Also tightened the
  `lllReducedCheck` docstring.

## Current frontier

Both PRs pushed. Two follow-up issues to file (Fin.foldl full-library
migration; fpLLL provider switch UX redesign). `det_colSwap` restatement
changed a public signature but had no callers.

## Next step

File the two issues, link them from the PRs. PR 2 targets PR 1's branch;
retarget to `main` once PR 1 merges.

## Blockers

None. Note: `HexManual` is not in `ci.yml`'s build list, so PR CI will not
catch manual regressions — `lake build HexManual` was run locally and is
green.
