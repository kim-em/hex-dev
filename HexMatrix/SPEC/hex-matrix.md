# hex-matrix (foundation, no dependencies)

Dense matrices over a coefficient type `R`.

**Contents:**
- `Matrix R n m`, an encapsulated dense matrix type. Consumers go through
  its API — `ofFn`, `ofRows`, `getRow`, `rows`, and entry access
  `M[(i, j)]` (the normal form for entries) — so the backing representation
  stays private and can change.
- Matrix-vector multiplication, matrix-matrix multiplication
- Dot product, norm squared (for `R = Int` and `R = Rat`)
- Row operations (swap, scale, add multiple of one row to another) and the
  corresponding column operations
- Submatrix / leading-submatrix slicing and the Gram matrix
- Generic over the coefficient type `R`

**Entry vs row access.** `M[(i, j)]` is the O(1) entry accessor and the normal
form for single entries. Row access `M[i]` is deliberately `noncomputable`: it
exists only so proofs may speak of whole rows, while compiled code reads rows
through the computable `getRow` and entries through `M[(i, j)]`. Any compiled
definition that reaches for `M[i]` fails to compile, so a future flat backing
representation never silently pays a per-entry row-materialization cost.

This is the dense base of the matrix family. The row-reduction stack
(`hex-row-reduce`), the Leibniz determinant theory (`hex-determinant`), and the
executable Bareiss algorithm (`hex-bareiss`) build on it.

**Elementary operations.** `rowSwap`, `rowScale`, `rowAdd`, `rowMoveUp`, and the
column analogues `colAdd` / `colAddRight` are pure data transforms on the dense
representation. Their algebraic identities (involutivity of `rowSwap`,
multiplicative behaviour `rowSwap_mul` / `rowScale_mul` / `rowAdd_mul`, and the
inverse-preservation lemmas) live here and are reused by row reduction and by
the determinant row-operation laws. They update the matrix in place when it is
uniquely referenced: each uses its argument linearly and goes through
`Vector.swap` / `Vector.modify` / `Vector.map`, which reuse the backing store
rather than copying it.

**Indexed row/column mutation.** `modifyRow` updates one row in place;
`setCol` and the per-entry `modifyCol` update one column entry per row. The
column operations share an in-place engine, `mapRowsIdx`, which threads the
matrix through a `Fin.foldl` of per-row `Vector.modify`s — no intermediate index
list is allocated, and each row's single-entry update reuses the freed row slot.
This replaces the former `ofFn`-rebuild form of `setCol`, which read and
reallocated every entry to change one column.

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
