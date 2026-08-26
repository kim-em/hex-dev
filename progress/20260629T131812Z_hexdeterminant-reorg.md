# HexDeterminant file reorganisation

## Accomplished

Restructured `HexDeterminant/` so file names track contents, not proof
technique, and so each subject lives in one place. No declaration was added,
removed, or renamed — `git`-diffing the full declaration-name set against HEAD
is empty. Whole graph builds green: `HexDeterminant` (88 jobs) and the full
downstream incl. Mathlib bridges (`HexDeterminantMathlib`, `HexBareiss*`,
`HexGramSchmidt`, `HexRowReduce*`), 2488 jobs.

Five moves:

- **Dropped `Expansion.lean`** (a 23-line re-export shell). Its consumers now
  import `Laplace`/`CauchyBinet` directly.
- **`Selection.lean` → `Gram.lean`** — the file is named for its deliverable
  (`det_gramMatrix_eq_sum_minors_sq`, `det_gramMatrix_nonneg`), not the internal
  strictly-increasing tuple enumeration.
- **Split `RowOps.lean` out of `Permutation.lean`.** `Permutation` keeps the
  S_n structure (transpositions, compose/inverse, `detSign` multiplicativity);
  `RowOps` holds the elementary-operation laws (`det_one`, `det_rowSwap`,
  `det_rowScale`, `det_rowAdd`, `det_transpose`, `cofactor_transpose`,
  `det_col*`). The four identity/rowScale helpers that supported those laws moved
  out of `Index`'s tail into `RowOps`.
- **Unified triangular results into `Triangular.lean`** — upper-triangular came
  from `Index`, lower-triangular from `Permutation`; they were the same subject
  split across two files. Lower-triangular needs `det_transpose` (RowOps) and
  the upper case, so `Triangular` sits after `RowOps`; `Gram` imports it.
- **Moved completeness/nodup to `Enumeration.lean`** — `permutationVectors_-`
  `complete`/`_nodup`/`_nodup_list` and their `raiseFinAbove`/`peelLastVector`
  plumbing are statements about the enumeration. This dragged a closed set of
  seven determinant-agnostic list/`Fin` helpers up from `Leibniz` (they are
  reused there via the `import all` chain).

Two follow-on cleanups in the same spirit:

- **`Index.lean` → `LastRow.lean`.** With completeness/nodup and triangular
  pulled out, the file holds only the last-row determinant recursion, so the
  vague "Index" name no longer fit. Its docstring was rewritten (the old one
  still described the moved-out `raiseFinAbove`/`peelLastVector` plumbing).
- **Shortened three slop names** flagged by the >=5-qualifier heuristic:
  `det_eq_det_principalSubmatrix_mul_last_of_last_row_zero` →
  `det_eq_principalSubmatrix_mul_last` (public, 2 internal call sites),
  `fin_mem_of_full_nodup_for_count` → `mem_of_full_nodup`, and the
  `foldl_det_sum_filter_split{,_start}` pair → `foldl_sum_filter_split{,_start}`
  (both private).

Import order is now:
`Enumeration → Leibniz → Minor → LastRow → Permutation → RowOps → ColumnLinear →
Laplace → CauchyBinet → Triangular → Gram → Adjugate → Plucker`.

## Current frontier

Branch `refactor/hexdeterminant-reorg`. Module docstrings for `Enumeration`,
`LastRow`, `Permutation` updated to match; others left as-is.

## Next step

Commit and open a PR if Kim wants it. The change is mechanical (pure relocation,
identical declaration set) so CI is the test plan.

## Blockers

None. One process note: the per-command `EXIT=$?`/notification exit codes
reflected a trailing `date` call, not `lake`; pass/fail must be read from the
build log's terminal line (`Build completed` vs `error: build failed`). An
extraction bug that swallowed each moved helper's following-decl docstring was
caught only by building the downstream graph, not by the (misread) green
notification — always confirm from the log text.
