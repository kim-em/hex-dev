# hex-determinant (depends on hex-matrix)

The generic Leibniz-formula determinant for dense square matrices, together with
the cofactor/adjugate theory, column-tuple (Cauchy-Binet) expansion, and the
Mathlib-free quadratic determinant identities: the two-row replacement identity
and the three-term Grassmann-Plücker relation.

**Definition.** Define `det` via the Leibniz formula (signed sum over
permutations), over any `Ring`. Theorems about `det` generally require
`CommRing`. The development is split by subject across `HexDeterminant/*`
(`Leibniz`, `Enumeration`, `Minor`, `LastRow`, `Permutation`, `RowOps`,
`ColumnLinear`, `Laplace`, `CauchyBinet`, `Triangular`, `Gram`, `Adjugate`,
`Plucker`), and `HexDeterminant.lean` re-exports all thirteen.

**Determinant of row operations.** The row-operation laws live here, since they
are statements about `det`. They are used by `hex-row-reduce` pivot-sign
tracking and by `hex-bareiss` for composing row swaps into a permutation sign.

**Key properties:**
- `det_identity : det (Matrix.identity n) = 1` (there is no matrix `One`
  instance, so the identity matrix is always written out)
- `det_rowSwap : i ≠ j → det (rowSwap M i j) = -det M`
- `det_rowScale : det (rowScale M i c) = c * det M`
- `det_rowAdd : src ≠ dst → det (rowAdd M src dst c) = det M`
- `det_mul : det (M * N) = det M * det N`
- column linearity, Laplace cofactor expansion, the Cauchy-Binet column-tuple
  product formula, the adjugate identity on both sides (`mul_adjugate` and
  `adjugate_mul`), and the quadratic identities specified below
- ordered rectangular selection through `selectedSubmatrix`, `selectedRows`,
  and `selectedColumnCoeffs`, with
  `det_selectedSubmatrix_mul_eq_sum_columnTuples` giving the selected-minor
  Cauchy--Binet expansion
- `mul_eq_one_comm : U * W = identity n → W * U = identity n` for a square
matrix over a commutative ring, proved through the adjugate (both
  `mul_adjugate` and `adjugate_mul` are needed). A one-sided inverse is
  therefore enough to witness invertibility, which is what the integer
normal-form certificate checkers are specified to rely on.

The permutation bridge used by selected-minor clients is public:
`ofFn_mem_permutationVectors`, `columnTupleMatrix_eq_ofFn_ofFn`, and
`det_columnTupleMatrix_of_injective` connect injective finite-index maps to the
column-tuple determinant API.

## Quadratic determinant identities: which name means what

Four classical names circulate for the quadratic relations among minors, and
they are *not* interchangeable. This SPEC and the sibling SPEC for
[hex-determinant-mathlib](https://github.com/leanprover/hex-determinant-mathlib/blob/main/SPEC/hex-determinant-mathlib.md)
use each in exactly one sense.

**Desnanot-Jacobi** (also Dodgson condensation, Lewis Carroll identity). For an
`(n+2) × (n+2)` matrix `M`, with `M^i_j` denoting deletion of row `i` and
column `j`:

```
det M * det M^{1,n+2}_{1,n+2} = det M^1_1 * det M^{n+2}_{n+2}
                              - det M^1_{n+2} * det M^{n+2}_1
```

Both distinguished rows and both distinguished columns are *deleted*.
`hex-determinant` states no theorem in this deletion form. Deletion-form
Desnanot-Jacobi exists only over Mathlib matrices, in
`hex-determinant-mathlib`.

**Jacobi's minor identity for the adjugate**, restricted to `2 × 2` minors. In
row-replacement rather than row-deletion form: for distinct rows `a`, `b` and
arbitrary replacement vectors `u`, `v`,

```
det M * det (M with rows a, b replaced by u, v)
  = det (M with row a := u) * det (M with row b := v)
  - det (M with row a := v) * det (M with row b := u)
```

This is what `hex-determinant` proves, as `det_setRow_setRow_mul_det`. It is
equivalent to Desnanot-Jacobi for an arbitrary row pair and column pair, in both
directions. Forwards, take `u = e_{j1}` and `v = e_{j2}` with `a < b` and
`j1 < j2`: each one-row replacement becomes a cofactor,
`det (setRow M a e_j) = cofactorSign a j * det (deleteRowCol M a j)`, and the
two-row replacement becomes the doubly-deleted minor with sign
`(-1)^(a + b + j1 + j2)`. That sign is common to all three products, so it
cancels and leaves Desnanot-Jacobi on rows `{a, b}` and columns `{j1, j2}`.
Backwards, both sides are bilinear in `(u, v)`, so expanding in the standard
basis reduces the general case to those basis pairs (the diagonal `j1 = j2`
terms vanish on both sides). It is **not** the general Sylvester determinant
identity; via that equivalence it is Sylvester's `2 x 2` case.

**Sylvester's determinant identity** is the general statement that an
`m x m` matrix of bordered minors has determinant `det A0 ^ (m - 1) * det A`,
and it is absent from both determinant libraries. Its exact
statement and proposed home are recorded in
[hex-determinant-mathlib](https://github.com/leanprover/hex-determinant-mathlib/blob/main/SPEC/hex-determinant-mathlib.md).
Nothing already in the tree proves it, so nothing already in the tree may be
renamed to claim it. The Bareiss recurrence uses only the case where the
bordered-minor matrix is `2 × 2`, and that case *is* Desnanot-Jacobi.

**Grassmann-Plücker relations** are the quadratic relations among the *maximal*
minors of a rectangular matrix. The three-term relation is the one this library
proves, and it is a statement about a tall matrix rather than about deleting a
row and a column of a square one.

### Index conventions for the Plücker surface

`HexDeterminant/Plucker.lean` fixes the following encoding, all `@[expose]`:

- `skipIndex2 p q hpq : Fin n → Fin (n + 2)` embeds while skipping two deleted
  indices `p.val < q.val`. The ordering proof `hpq` is a phantom argument: it
  pins the precondition at call sites but is not consumed, which deliberately
  trips the `unusedArguments` linter.
- `mMatrix B v p : Matrix R (n + 1) (n + 1)` for `B : Matrix R (n + 2) n` and
  `v : Vector R (n + 2)` is `[B | v]` with row `p` deleted; columns `0..n-1`
  carry `B`, the last column carries `v`. `mDet B v p := det (mMatrix B v p)`.
- `nMatrix B p q hpq : Matrix R n n` is `B` with rows `p` and `q` deleted, in
  increasing-row order. `nDet B p q hpq := det (nMatrix B p q hpq)`.
- `twoColMatrix B u v` / `twoColDet B u v` append two vector columns instead of
  one, and expand back onto `mDet` through `twoColDet_eq_sum_mDet`.

### The public identity theorems

Every declaration below is exported by the `HexDeterminant` umbrella, over
`[Lean.Grind.CommRing R]`.

Two-row replacement, in `HexDeterminant/Adjugate.lean`:

```lean
theorem det_setRow_setRow_mul_det
    (M : Matrix R (n + 1) (n + 1)) (a b : Fin (n + 1)) (hab : a ≠ b)
    (u v : Vector R (n + 1)) :
    det M * det (setRow (setRow M a u) b v) =
      det (setRow M a u) * det (setRow M b v) -
        det (setRow M a v) * det (setRow M b u)
```

with `cofactorRowPairing_setRow_plucker` the same identity one step earlier,
before `det_setRow_eq_cofactorRowPairing` rewrites each side into determinants.

The only hypothesis is `a ≠ b`. The replacement vectors are unconstrained, and
there is no nondegeneracy or integral-domain assumption: the proof runs through
`det_mul_cofactor_setRow_eq`, which evaluates a single entry of
`adjugate (setRow M a u) * (setRow M a u * adjugate M)` two ways. One
association uses `adjugate_mul_apply`; the other splits the sum over rows with
`setRow_mul_adjugate_apply_self` and `_ne`, whose off-replacement case is
`cofactorRowPairing_self` on the diagonal and `cofactorRowPairing_alien_eq_zero`
off it. The `det M` factor is *produced* by that split rather than cancelled.

Mathlib's `desnanot_jacobi` reaches the same generality by a different route,
proving the identity over an integral domain and then transferring it along an
`MvPolynomial` evaluation from the universal matrix.

Three-term Grassmann-Plücker, in `HexDeterminant/Plucker.lean`:

```lean
theorem det_plucker_three_term_consecutive_top
    (B : Matrix R (k + 2) k) (v : Vector R (k + 2))
    (alpha : Fin (k + 2)) (halpha : alpha.val < k) :
    let pk : Fin (k + 2) := ⟨k, _⟩
    let plast : Fin (k + 2) := Fin.last (k + 1)
    mDet B v alpha * nDet B pk plast _ -
      mDet B v pk * nDet B alpha plast _ +
      mDet B v plast * nDet B alpha pk _ = 0
```

This is the *consecutive-top* specialisation: the three distinguished rows are
`alpha`, `k`, and `k+1` inside `Fin (k + 2)`, so the largest is the last row of
`B` and the case `q > p3` cannot arise. Removing that case is what makes the
Mathlib-free proof tractable; it is a proof-effort restriction, not a
mathematical one. The unrestricted three-term relation, for arbitrary
`p1 < p2 < p3`, is `det_plucker_three_term` in `hex-determinant-mathlib`; it is
not restated here.

Supporting public lemmas, all in `Plucker.lean`, that a consumer of the
three-term relation is expected to use rather than re-derive:
`mDet_eq_sum_unit` and `twoColDet_eq_sum_unit_pairs` (basis expansion of the
appended columns), `det_eq_signed_minor_of_col_basis` (Laplace along a basis
column), `mDet_unit_eq_signed_nDet_of_lt` / `_of_gt` /
`mDet_unit_eq_zero_of_eq` and `twoColDet_unit_unit_of_lt` / `_of_gt` / `_of_eq`
(the ordered basis-pair evaluations, including the sign), and
`deleteRowCol_mMatrix_at_q_minus_one_eq_nMatrix_of_lt` /
`deleteRowCol_mMatrix_at_q_eq_nMatrix_of_gt` (identifying a deleted `mMatrix`
with the corresponding `nMatrix`, on the two sides of the `q < p` split).

**Mathlib-free vs. Mathlib proof surface.** Theorems connecting `Hex.det`
to Mathlib's `Matrix.det` (e.g. `det_eq : Hex.det M = Matrix.det (matrixEquiv M)`)
live exclusively in the sibling `*-mathlib` layer and **must not** be
restated, reproven, or specialized inside `hex-determinant`. The translation
that connects the executable Bareiss determinant to this Leibniz `det`
(`bareiss_eq_det` and the Desnanot-Jacobi bordered-minor invariant) is specified
in `hex-bareiss`; the proof itself lives in `hex-determinant-mathlib` and
`hex-bareiss-mathlib`.

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
