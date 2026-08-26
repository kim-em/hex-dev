# HexRowReduce Performance Report

`HexRowReduce` provides the executable row-reduction stack over the `HexMatrix`
dense core: the row-echelon transform and its elementary-operation contracts
(`RowEchelon`), and the executable RREF loop with its pivot/free-column
partition and span/nullspace APIs (`RREF`).

## Bench Targets

None. The row-reduction surface has no performance-critical headline benchmark:
its operations (`rref`, `rref_rank`, `nullspace`, `spanCoeffs`) are exact
rational computations whose cost is dominated by `Rat` arithmetic, and they are
validated for correctness rather than timed against an external tool.

## Comparators

`HexRowReduce` declares no Phase-4 external comparator. Correctness of the
`rank`, `rref`, and `nullspace` operations is cross-checked against
python-flint's `fmpz_mat` / `fmpq_mat` through the conformance oracle
`scripts/oracle/matrix_flint.py` (driven by `hexrowreduce_emit_fixtures`): the
oracle confirms the rational rank, the unique reduced row echelon form, and the
right-kernel basis (each basis vector annihilated by the source matrix, with the
nullity matching `m - rank`).

## Verdicts

The conformance oracle passes on every committed fixture
(`conformance-fixtures/HexRowReduce/rowreduce.jsonl`: nine matrices at the
4×4 / 6×6 / 8×8 bands in random, singular, and triangular shapes, each checked
for `rank`, `rref`, and `nullspace`). The in-Lean `#guard` conformance module
additionally checks the executable span/nullspace API on committed examples.

## Concerns

None. Row reduction is a correctness surface here, not a performance-tuned one.
