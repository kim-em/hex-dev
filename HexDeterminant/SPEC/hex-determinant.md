# hex-determinant (depends on hex-matrix)

The generic Leibniz-formula determinant for dense square matrices, together with
the cofactor/adjugate theory, column-tuple (Cauchy-Binet) expansion, and the
two-row Plücker / Desnanot-Jacobi identities.

**Definition.** Define `det` via the Leibniz formula (signed sum over
permutations), over any `Ring`. Theorems about `det` generally require
`CommRing`. The development is split by subject across `HexDeterminant/*`
(`Leibniz`, `Enumeration`, `Minor`, `Index`, `Permutation`, `ColumnLinear`,
`Laplace`, `CauchyBinet`, `Expansion`, `Selection`, `Adjugate`, `Plucker`).

**Determinant of row operations.** The row-operation laws live here, since they
are statements about `det`. They are used by `hex-row-reduce` pivot-sign
tracking and by `hex-bareiss` for composing row swaps into a permutation sign.

**Key properties:**
- `det_one : det 1 = 1`
- `det_rowSwap : i ≠ j → det (rowSwap M i j) = -det M`
- `det_rowScale : det (rowScale M i c) = c * det M`
- `det_rowAdd : i ≠ j → det (rowAdd M i j c) = det M`
- column linearity, Laplace cofactor expansion, the Cauchy-Binet column-tuple
  product formula, the adjugate identity, and the Plücker / Desnanot-Jacobi
  two-row identities

**Mathlib-free vs. Mathlib-bridge proof surface.** Theorems connecting `Hex.det`
to Mathlib's `Matrix.det` (e.g. `det_eq : Hex.det M = Matrix.det (matrixEquiv M)`)
live exclusively in the sibling `*-mathlib` bridge layer and **must not** be
restated, reproven, or specialized inside `hex-determinant`. The bridge that
connects the executable Bareiss determinant to this Leibniz `det`
(`bareiss_eq_det` and the Desnanot-Jacobi bordered-minor invariant) is specified
in `hex-bareiss`; the proof itself lives in the Mathlib bridge layer.

## External comparators

The Leibniz determinant has no external comparator: it is the reference
combinatorial definition, cross-checked for agreement against the row-pivoted
Bareiss determinant (`hex-bareiss`) and against python-flint's `fmpz_mat.det`
through the conformance oracle (`scripts/oracle/matrix_flint.py`, driven by
`hexdeterminant_emit_fixtures`). It declares external-comparator absence for the
Phase-4 bench surface (`runLeibnizDet`) with the **structural-layer** reason. See
`reports/hex-determinant-performance.md` and the project
[`libraries.yml`](https://github.com/kim-em/hex-dev/blob/main/libraries.yml)
under `HexDeterminant.phase4`.
