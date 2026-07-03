# Phase 6 closeout — HexMatrixMathlib + HexGramSchmidtMathlib (#8262/#8263/#8265)

**Accomplished**
- Discovered #8262/#8265 were premised on a HexMatrixMathlib structure that
  no longer exists: the `Determinant/` subtree, `RankSpanNullspace.lean`,
  `bareiss_eq_det`, and the 23 named unreferenced theorems were all removed
  when `Hex.Matrix` was encapsulated behind a one-field structure (#8442) and
  the docs rewritten (#8479/#8486). Retargeted the *goal* (Phase 6 closeout +
  bump) onto the current files.
- Calibrated the linter/dead-code bar against the done_through-6 sibling
  HexPolyZMathlib (the exact pattern #8260 established): simpNF findings are
  tolerated (the sibling carries 13), and unreferenced *public* documented
  correspondence lemmas are kept as Mathlib-facing API (the sibling carries
  15 public / 0 private).
- HexMatrixMathlib: already clean (0 orphans, docBlame 0, no warnings, one
  tolerated simpNF on `matrixEquiv_symm_apply`). Closeout is the bump.
- HexGramSchmidtMathlib: fixed 2 build-time `unusedSimpArgs` warnings
  (`RowAdd.lean` 191/194), excised 5 unreferenced private orphans
  (`scaledCoeffMatrix_bareiss_eq_det`,
  `scaledCoeffMatrix_replacementColumn_solve_intGram` and its now-orphaned
  helper `dot_basisPrefixProjection_eq_castIntGram`, `scaledCoeffRows_lower_eq_coeffs`
  [superseded by the adjacent public `scaledCoeffs_eq`], `rowAdd_row_at`),
  leaving 4 public / 0 private orphans — matching the sibling profile.
- Bumped both `done_through: 5 → 6`. `lake build` green with zero warnings;
  `check_dag` exit 0; `status.py` now lists both under Phase 7.

**Current frontier**
- Both bridge libraries are at Phase 6. Their Phase 7 (reference-manual
  chapters) is the next step, tracked separately.

**Next step**
- Close #8265 (obsolete — its 23-theorem target was removed by #8442) and
  #8262/#8263 (delivered via this retargeted closeout).

**Blockers**
- None.
