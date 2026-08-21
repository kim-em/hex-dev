# hex-determinant-mathlib (depends on hex-determinant + hex-bareiss + hex-matrix-mathlib + Mathlib)

Mathlib layer for `hex-determinant`: proves that our executable Leibniz
determinant corresponds to Mathlib's `Matrix.det`, assembles the Desnanot-Jacobi
identity in the bordered-minor form the Bareiss correctness proof consumes, and
proves the unrestricted three-term Grassmann-Plücker relation (which nothing in
the tree consumes yet).

**Determinant correspondence:**
```lean
theorem det_eq (M : Hex.Matrix R n n) :
    Hex.det M = Matrix.det (matrixEquiv M)
```

Through `det_eq`, Mathlib determinant theorems (Cramer's rule, Cauchy-Binet,
adjugate identities) transfer to our executable determinant.

## Module layout and export chain

Everything lives in the `HexMatrixMathlib` namespace, except `desnanot_jacobi`,
which is in the root namespace because it is upstream Mathlib content. Two
sub-namespaces sit inside it: `HexMatrixMathlib.PermutationVector` (the
permutation-sign transport, including `toPerm`, `equivs` and
`detSign_eq_permSign`) and `HexMatrixMathlib.OrderedFourShift` (the cycle
helpers for the four-row transport).

| module | contents |
|---|---|
| `DesnanotJacobi` | the pure-Mathlib `desnanot_jacobi`, no Hex dependency |
| `CoreTransport` | permutation-sign transport, `det_eq`, submatrix transport, the Hex-side Desnanot-Jacobi forms, the one-row and two-row replacement identities, and the ordered four-row `nMatrix` helpers |
| `CorePlucker` | the three-term Grassmann-Plücker assembly and the Bareiss bordered-minor Desnanot-Jacobi specialisation |
| `Core` | re-exports `CoreTransport` and `CorePlucker` |

The umbrella `HexDeterminantMathlib.lean` imports `Core` only. `DesnanotJacobi`
reaches it transitively, through `CoreTransport`'s `public import`, so
`desnanot_jacobi` *is* part of the umbrella's export surface even though no
module names it in an import list next to `Core`. That chain is load-bearing:
`DesnanotJacobi` has no other importer, so dropping the `public` from
`CoreTransport`'s import of it would silently remove `desnanot_jacobi` from the
umbrella's export surface. The module would still exist and stay directly
importable as `HexDeterminantMathlib.DesnanotJacobi`, which is exactly what
makes the regression easy to miss.

`DesnanotJacobi.lean` was copied verbatim from commit `bbe9ab491bc1` of
https://github.com/leanprover-community/mathlib4/pull/37716
("feat(LinearAlgebra/Matrix/Determinant): Desnanot-Jacobi identity", by Slava
Naprienko) and carries its own copyright header. It is no longer verbatim: it
has since been migrated to the `module` / `public import` system and had two
`simp` sets repaired across toolchain bumps. It is to be deleted in favour of
the upstream module once that PR merges, and the upstream branch has itself
moved on from the pinned commit, so expect to re-check the statement rather
than assume a drop-in swap. Everything in the file except the final theorem is
`private`.

## Desnanot-Jacobi: the four public forms

The identity is stated once and then transported. Each form below is public and
reachable from the umbrella.

`desnanot_jacobi` (root namespace, `DesnanotJacobi`), over any `CommRing`, with
no hypothesis on `M`. The two distinguished rows and columns are pinned to the
first and last index of `Fin (n + 2)`; deletion is by `Fin.succAbove`, and the
interior minor is the double deletion
`Fin.succAbove 0 ∘ (Fin.last n).succAbove`:

```lean
theorem desnanot_jacobi {R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin (n + 2)) (Fin (n + 2)) R) :
    M.det * (M.submatrix (Fin.succAbove 0 ∘ (Fin.last n).succAbove)
      (Fin.succAbove 0 ∘ (Fin.last n).succAbove)).det =
    (M.submatrix (Fin.succAbove 0) (Fin.succAbove 0)).det *
      (M.submatrix (Fin.last (n + 1)).succAbove (Fin.last (n + 1)).succAbove).det -
    (M.submatrix (Fin.succAbove 0) (Fin.last (n + 1)).succAbove).det *
      (M.submatrix (Fin.last (n + 1)).succAbove (Fin.succAbove 0)).det
```

`desnanot_jacobi_matrixEquiv_reindex` (`CoreTransport`) takes an arbitrary pair
of `Equiv.Perm`s `row` and `col` and states the same identity for
`(matrixEquiv M).submatrix row col`. This is the form to use when the two
distinguished rows and columns are not the endpoints. Mind the direction:
`submatrix` composes, so `row` maps *new* indices to original ones. To
distinguish original rows `r1` and `r2`, pick `row` with `row 0 = r1` and
`row (Fin.last (n + 1)) = r2`, equivalently `row.symm` carrying `r1` and `r2`
to the endpoints.

`desnanot_jacobi_deleteRowCol_endpoints` (`CoreTransport`) is the endpoint case
restated entirely in Hex terms, with `Hex.Matrix.deleteRowCol` in place of
`Matrix.submatrix` and the interior minor written as an iterated
`deleteRowCol M 0 0` then `deleteRowCol _ (Fin.last n) (Fin.last n)`. Note the
index shift between the two deletions: the outer one indexes into
`Fin (n + 2)`, the inner into `Fin (n + 1)`.

`desnanot_jacobi_borderedMinor` (`CorePlucker`) is the Bareiss step form, and
the one every consumer in the tree actually uses:

```lean
theorem desnanot_jacobi_borderedMinor [CommRing R]
    (source : Hex.Matrix R n n) (k : Nat) (hk : k < n) (hnext : k + 1 < n)
    (i j : Fin n) (hi : k < i.val) (hj : k < j.val) :
    det (borderedMinor source (k + 1) hnext i j) *
        det (principalSubmatrix source k (Nat.le_of_lt hk)) =
      det (borderedMinor source k hk ⟨k, _⟩ ⟨k, _⟩) *
          det (borderedMinor source k hk i j) -
        det (borderedMinor source k hk i ⟨k, _⟩) *
          det (borderedMinor source k hk ⟨k, _⟩ j)
```

Writing `b(r, c) := det (borderedMinor source k hk r c)` for the minor on rows
`{0, …, k-1, r}` and columns `{0, …, k-1, c}`, this says

```
b'(i, j) * det (principalSubmatrix source k) = b(k, k) * b(i, j) - b(i, k) * b(k, j)
```

where `b'` is the same construction one level up. The right-hand side is the
determinant of the `2 × 2` matrix of bordered minors indexed by rows `{k, i}`
and columns `{k, j}`, so this is exactly the `2 × 2` case of Sylvester's
identity below.

The reindexing that gets from `desnanot_jacobi` to that shape is
`bareissDesnanotIndex k : Fin (k + 2) ≃ Fin (k + 2)`, which permutes the
bordered minor into the order `[k, 0, 1, …, k-1, k+1]` so that Desnanot-Jacobi
deletes the Bareiss pivot row and column first and the trailing row and column
last, leaving the previous leading principal minor as the interior.
`det_borderedMinor_bareissDesnanotIndex` records that the reindexing is
determinant-preserving, and `desnanot_jacobi_borderedMinor_reindex` is the
intermediate statement in reindexed Mathlib coordinates.

Consumers: `HexBareissMathlib/Bareiss.lean` (twice) and
`HexGramSchmidtMathlib/Int/Augmented.lean`. `bareissExactDiv_borderedMinor_of_mul_eq`
packages the resulting product identity as the `hexact` premise of
`Hex.Matrix.stepMatrix_borderedMinor_update`; it takes the identity as the
hypothesis `hdesnanot` and additionally requires `prevPivot ≠ 0`, the only
nondegeneracy hypothesis anywhere in this surface.

## Two-row replacement and Grassmann-Plücker

`det_mul_cofactor_setRow_eq_cofactorRowPairing_mul_sub` (one row replaced) and
`det_mul_det_setRow_setRow_eq_cofactorRowPairing_mul_sub` (two rows replaced)
restate the adjugate row-replacement identities in Hex terms, obtained from
Mathlib's `Matrix.adjugate` theory. The two-row one has hypothesis `s ≠ r` and
is the cofactor-pairing form of the `hex-determinant` theorem
`det_setRow_setRow_mul_det`; the two are the same mathematical statement proved
twice, once through Mathlib and once Mathlib-free, with the subtracted products
written in opposite factor order (equal by `mul_comm`). The Mathlib route landed
first (PR #6048), the Mathlib-free one shortly after (PR #6111), so the copy here
is now redundant in principle and could be re-derived from
`Hex.Matrix.det_setRow_setRow_mul_det`. Doing so is a refactor, not a
correctness question, and nothing turns on it.

`det_plucker_three_term` is the unrestricted three-term Grassmann-Plücker
relation, for arbitrary ordered `p1 < p2 < p3`:

```lean
theorem det_plucker_three_term
    {R : Type u} [CommRing R] {n : Nat}
    (B : Hex.Matrix R (n + 3) (n + 1)) (v : Vector R (n + 3))
    (p1 p2 p3 : Fin (n + 3))
    (h12 : p1.val < p2.val) (h23 : p2.val < p3.val) :
    mDet B v p1 * nDet B p2 p3 h23 -
      mDet B v p2 * nDet B p1 p3 (Nat.lt_trans h12 h23) +
      mDet B v p3 * nDet B p1 p2 h12 = 0
```

The `mDet` / `nDet` index conventions are fixed in `hex-determinant` and are not
restated here. The dimensions are `(n + 3) × (n + 1)`, one taller and one
narrower than a square matrix, because `mDet` appends the column `v` and `nDet`
deletes two rows. `hex-determinant` proves the Mathlib-free
`det_plucker_three_term_consecutive_top`, which is the specialisation with
`p2 = k` and `p3 = k + 1` in `Fin (k + 2)`.

The assembly runs, in `CorePlucker`, from the ordered four-row kernel
`ordered_four_det_mul_det_setRow_setRow_eq_cofactorRowPairing_mul_sub` through
`det_double_setRow_eq_pow_mul_nDet` and `ordered_four_signed_Plucker_p1_side` to
`det_plucker_three_term_nDet_of_ordered_four`, then splits on the position of a
basis-vector row `q` (`det_plucker_three_term_basisVec_of_ne` plus the three
diagonal cases) and finally expands `v` in the standard basis. Nothing in the
tree consumes `det_plucker_three_term` yet; it is public API for downstream
consumers of the released library.

## Sylvester's determinant identity: absent

The general Sylvester identity is **not** proved anywhere in this project, and
no existing theorem should be renamed to claim it. It states: for
`A` square of size `k + m`, let `A₀` be the leading `k × k` principal submatrix
and let `b i j` for `i j : Fin m` be the bordered minor on rows
`{0, …, k-1} ∪ {k + i}` and columns `{0, …, k-1} ∪ {k + j}`. Then the `m × m`
matrix of bordered minors has determinant `det A₀ ^ (m - 1) * det A`.

Stated at `m + 1` to avoid truncated subtraction, and with the border map
written out:

```lean
/-- `Fin (k + 1) → Fin (k + (m + 1))`: the leading `k` indices, then `k + i`. -/
def borderIndex (k m : ℕ) (i : Fin (m + 1)) (r : Fin (k + 1)) :
    Fin (k + (m + 1)) :=
  if h : r.val < k then Fin.castAdd (m + 1) ⟨r.val, h⟩ else Fin.natAdd k i

theorem det_sylvester {R : Type*} [CommRing R] {k m : ℕ}
    (A : Matrix (Fin (k + (m + 1))) (Fin (k + (m + 1))) R) :
    (Matrix.of fun i j : Fin (m + 1) =>
        (A.submatrix (borderIndex k m i) (borderIndex k m j)).det).det =
      (A.submatrix (Fin.castAdd (m + 1)) (Fin.castAdd (m + 1))).det ^ m * A.det
```

At `m = 0` both sides are `det A`. At `m = 1` the left-hand side is
`b 0 0 * b 1 1 - b 0 1 * b 1 0` and the right-hand side is `det A₀ * det A`,
which is Desnanot-Jacobi in bordered-minor form. Instantiating that case with
`A` the `(k + 2) × (k + 2)` submatrix of `source` on rows `{0, …, k, i}` and
columns `{0, …, k, j}` reproduces `desnanot_jacobi_borderedMinor`: `A₀` becomes
`principalSubmatrix source k`, the four `b` entries become the four
`borderedMinor source k` determinants, and `det A` becomes
`det (borderedMinor source (k + 1) _ i j)`. That correspondence is
term-for-term modulo the submatrix transports already in `CoreTransport` and one
`mul_comm` on the subtracted product.

The statement above is not proved here, but it does elaborate at current `main`,
and the formula was checked by kernel evaluation over `ℤ` at
`(k, m) = (1, 1)`, `(1, 2)` and `(2, 1)` before being written down.

**Proposed home.** A new `HexDeterminantMathlib/Sylvester.lean`, stated over
Mathlib matrices with no Hex dependency, following the `DesnanotJacobi.lean`
precedent of holding pure-Mathlib content pending an upstream contribution, and
re-exported by a `public import` from `CoreTransport` so it reaches the
umbrella. A Hex-side `sylvester_borderedMinor` would then belong next to
`desnanot_jacobi_borderedMinor` in `CorePlucker.lean`, using the same
`borderedMinor` / `principalSubmatrix` encoding.

**Not a prerequisite for anything.** Fraction-free elimination needs only the
`m = 1` case, one step at a time, which is what `desnanot_jacobi_borderedMinor`
already provides. The general identity would be worth proving as a statement
about `Matrix.det` in its own right, not to unblock a consumer. It must not be
folded into the Bareiss correctness path as a substitute for the existing
Desnanot-Jacobi step, which is strictly cheaper to state and to apply.
