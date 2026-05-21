# HexMatrix RREF API Phase 6 Review

Scope: `HexMatrix/RowEchelon.lean` and `HexMatrix/RREF.lean`, checked
against `SPEC/Libraries/hex-matrix.md` and `PLAN/Phase6.md`.

## Findings

Follow-up needed.

- `IsEchelonForm.spanCoeffs_sound` and `IsEchelonForm.spanContains_sound`
  require `E.HasNonzeroPivots`, but `spanCoeffs_sound` does not use the
  hypothesis: the definition already verifies `rowCombination M coeffs = v`
  before returning `some coeffs`. This makes soundness harder to apply than it
  needs to be for general echelon data, and callers that only need one-way
  soundness should not have to prove a pivot nonzero side condition.

- The public wrapper `Matrix.spanCoeffs` has no direct soundness theorem. Users
  can combine `rref_isRREF` with the internal `IsEchelonForm.spanCoeffs_sound`,
  or route through `Matrix.spanContains_iff`, but the natural theorem shape
  `Matrix.spanCoeffs M v = some c -> rowCombination M c = v` is absent. The
  conformance file therefore checks the returned coefficients by a separate
  executable equality instead of applying a named theorem.

- `rref` exposes its correctness almost entirely through the bundled
  `rref_isRREF` proof. That is a good primary contract, but the basic
  characterising projections for the computed data are private
  (`rref_transform_mul`, `rref_rank_le_n`, `rref_rank_le_m`,
  `rref_pivotCols_sorted`). Downstream users can recover them by applying
  structure fields of `rref_isRREF M`, but Phase 6 would be cleaner with public
  wrapper lemmas for the common facts about `(rref M).transform`,
  `(rref M).rank`, and `(rref M).pivotCols`.

- The nullspace API has good public vector-entry lemmas for `IsRREF.nullspace`
  (`nullspace_get_free`, `nullspace_get_free_ne`, `nullspace_get_pivot`), but
  the corresponding matrix-entry lemmas for `IsRREF.nullspaceMatrix` are
  private. `HexMatrixMathlib/RankSpanNullspace.lean` works around this with
  local helper lemmas and unfolding. Exposing the matrix-entry characterisation
  would reduce bridge-layer unfolding and match the SPEC's primary
  `nullspaceMatrix` surface.

- The public convenience `Matrix.nullspaceBasisMatrix` has soundness and
  completeness through `Matrix.nullspace_sound` and `Matrix.nullspace_complete`,
  but it has no public bridge theorem relating its columns to
  `Matrix.nullspace M`. Downstream Berlekamp proof code currently proves a
  private `nullspaceBasisMatrix_entry_eq_basis_coeff` by unfolding
  `Matrix.IsRREF.nullspace`. A public column or entry lemma would avoid that
  definitional dependency.

## Proposed Follow-Up Issues

- `HexMatrix Phase 6: remove unnecessary pivot hypothesis from span soundness`
- `HexMatrix Phase 6: add public Matrix.spanCoeffs_sound wrapper`
- `HexMatrix Phase 6: expose rref projection lemmas for transform, rank, and pivots`
- `HexMatrix Phase 6: make nullspaceMatrix entry characterisation public`
- `HexMatrix Phase 6: relate Matrix.nullspaceBasisMatrix columns to Matrix.nullspace`

## Checks

- Public row and column operation declarations have docstrings and useful
  entry/row/column characterising lemmas. Existing `[simp]` annotations are
  concentrated on normalization lemmas rather than broad conditional entry
  expansions, which is appropriate.
- `RowEchelonData`, `IsEchelonForm`, and `IsRREF` match the SPEC shape and keep
  determinant/Bareiss bridge obligations out of the row-reduction review
  surface.
- The free-column partition API (`freeCols_sorted`, `colPartition`,
  `colPartition_exclusive`, `pivotCols_injective`, `freeCols_injective`,
  `pivotCols_disjoint_freeCols`) covers the SPEC's column-partition contract.
- Source edits are intentionally deferred to follow-up issues; this review only
  adds the report.

## Residual Risk

This audit was limited to API shape, theorem accessibility, docstring coverage,
and downstream unfold pressure for row-echelon/RREF/span/nullspace declarations.
It did not review Bareiss determinant correctness, Gram-Schmidt consumers, or
performance behavior beyond noting existing RREF/nullspace use sites.
