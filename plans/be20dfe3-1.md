## Current state

`HexPolyMathlib/Basic.lean` (the executable-`DensePoly` ↔ Mathlib
`Polynomial` bridge) has a cluster of **undocumented** `private`
helper declarations spanning lines ~28–194. They build the
fold-over-diagonals model of polynomial-multiplication coefficients
that underwrites `coeff_toPolynomial` and the `mulCoeffSum`
characterisation. Each currently has no preceding `/-- … -/`
docstring. This is part of the library's Phase 6 (proof polishing)
docstring-coverage exit criterion.

The 14 declarations in the cluster (verify line numbers at claim
time; they drift as the file changes):

- `list_getD_map_range_zero`
- `denseDiagonalMulCoeffTerm` (def)
- `denseBoundedDiagonalMulCoeffTerm` (def)
- `fold_mulCoeffStep_eq_bounded_diagonal`
- `fold_mulCoeffStep_eq_diagonal`
- `fold_mulCoeff_outer_eq_diagonal`
- `mulCoeffSum_eq_diagonal`
- `denseDiagonalMulCoeffTerm_eq_zero_of_size_le`
- `fold_diagonal_extend`
- `diagonalSum_eq_bound`
- `denseDiagonalMulCoeffTerm_eq_zero_of_degree_lt`
- `fold_diagonal_truncate_degree`
- `diagonalSum_eq_degree_bound`
- `range_foldl_add_eq_finset_sum`

## Deliverables

1. Add a one- to three-sentence `/-- … -/` docstring to each of the
   14 declarations above, stating what it proves (or, for the two
   `def`s, what term it denotes) and its role in the
   diagonal-sum / fold model of `DensePoly` multiplication
   coefficients (i.e. how it feeds `mulCoeffSum_eq_diagonal` and the
   downstream `coeff_toPolynomial` / `coeff_mul`-style bridge).
2. Doc-only change: do **not** touch any signature, statement, proof,
   `simp`/`grind` attribute, declaration order, or `private`
   modifier. Additions to the file must be docstring lines only.

## Context

- This matches the established "Phase 6 docstrings for the … helper
  cluster" issue pattern (e.g. the recently merged HexMatrix /
  HexPolyZ / HexLLL batches). Keep each docstring crisp; describe the
  *thing*, not the proof tactics.
- `HexPolyMathlib` imports Mathlib, so its build is slower than the
  Mathlib-free libraries. Build the single module, not the whole
  Mathlib layer.
- Phase 6 doc rule: `SPEC/design-principles.md` (docstring coverage
  for public declarations and non-obvious private helpers);
  `PLAN/Phase6.md` (exit criteria).
- If you find the cluster has already been documented (a racing PR
  landed first), `coordination skip` with that note rather than
  forcing trivial edits.

## Verification

- `lake build HexPolyMathlib.Basic`: green.
- `git diff --numstat -- HexPolyMathlib/Basic.lean`: additions only
  (`N 0`).
- `git diff --check`: clean.
- Added-line grep finds no `sorry` / `axiom` / `native_decide` /
  `TODO` / `FIXME`.
- `python3 scripts/check_dag.py`: exit 0.
