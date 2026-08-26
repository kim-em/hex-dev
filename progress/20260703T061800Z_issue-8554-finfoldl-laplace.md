# Issue #8554: migrate List.finRange folds to Fin.foldl (step 1)

## Accomplished

First PR in the `List.finRange`-fold → `Fin.foldl` migration series. Did
step 1 from the issue: the public reader-facing determinant statements.

- `HexDeterminant/Laplace.lean`: made `det_eq_finFoldl_laplace_col` and
  `det_eq_finFoldl_laplace_row` the primary `Fin.foldl` statements (mirroring
  the `finFoldl` / `foldl` convention already in `Triangular.lean`). The old
  `det_eq_foldl_laplace_col` / `det_eq_foldl_laplace_row` names survive
  unchanged as thin `List.finRange` corollaries via
  `Fin.foldl_eq_finRange_foldl`, so downstream (`Adjugate`, `Plucker`,
  `GramDet`) is 100% untouched. Building-block `_last` / `_last_row` theorems
  left in list form.
- Manual (`HexManual/Chapters/HexDeterminant.lean`): repointed the cofactor
  docstring to `det_eq_finFoldl_laplace_row` and the triangular docstring to
  the already-existing `det_upperTriangular_eq_finFoldl_diag`.
- `HexDeterminant/README.md`: headline Laplace example now shows the
  `Fin.foldl` form, with a note on the list reference form.

Full determinant lib + manual chapter build green. Second opinion (Codex)
validated direction and scope; its only actionable flag (the README headline)
is addressed.

## Current frontier

Public determinant API is now `Fin.foldl`-canonical. The `@[csimp]` bridges,
compiled forms, and `#guard`s are untouched (change is statement-level only).

## Next step

Step 2 of the issue: internal reasoning lemmas, file by file, as separate PRs
in the series (`MatrixAlgebra`, `DotProduct`, `ColumnLinear`, `CauchyBinet`,
`LastRow`, `Enumeration`). Caveat: folds over `permutationVectors` /
`columnTupleVectors` stay `List.foldl`.

## Blockers

None.
