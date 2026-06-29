# hex-matrix (foundation, no dependencies)

Dense matrices as `Vector (Vector R m) n`.

**Contents:**
- `Matrix R n m` := `Vector (Vector R m) n` (uses stdlib `Vector`)
- Matrix-vector multiplication, matrix-matrix multiplication
- Dot product, norm squared (for `R = Int` and `R = Rat`)
- Row operations (swap, scale, add multiple of one row to another) and the
  corresponding column operations
- Submatrix / leading-submatrix slicing and the Gram matrix
- Generic over the coefficient type `R`

This is the dense base of the matrix family. The row-reduction stack
(`hex-row-reduce`), the Leibniz determinant theory (`hex-determinant`), and the
executable Bareiss algorithm (`hex-bareiss`) build on it.

**Elementary operations.** `rowSwap`, `rowScale`, `rowAdd`, `rowMoveUp`, and the
column analogues `colAdd` / `colAddRight` are pure data transforms on the dense
representation. Their algebraic identities (involutivity of `rowSwap`,
multiplicative behaviour `rowSwap_mul` / `rowScale_mul` / `rowAdd_mul`, and the
inverse-preservation lemmas) live here and are reused by row reduction and by
the determinant row-operation laws.

**Key properties:**
- identity matrices act as left and right multiplicative identities
- `transpose` is involutive
- `gramMatrix M = M * Mᵀ`
- elementary-operation multiplicative and inverse-preservation lemmas

The determinant of a row operation (`det_rowSwap`, `det_rowScale`,
`det_rowAdd`) is stated in `hex-determinant`, where `det` is defined.

## External comparators

The dense base surfaces (matrix multiplication, row operations, transposition,
slicing) have **no** external comparator named. They declare absence with the
**structural-layer** reason per
[the benchmarking spec's "Comparator naming" section](https://github.com/kim-em/hex-dev/blob/main/SPEC/benchmarking.md#comparator-naming):
those surfaces are GMP-backed `Int` arithmetic on `Vector` / `Array`
primitives. The determinant comparator (FLINT `fmpz_mat_det`) covers the
determinant surface and lives in `hex-bareiss`.

Structured metadata in the project's
[`libraries.yml`](https://github.com/kim-em/hex-dev/blob/main/libraries.yml)
under `HexMatrix.phase4`.
