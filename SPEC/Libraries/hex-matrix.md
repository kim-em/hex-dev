# hex-matrix (foundation, no dependencies)

Dense matrices as `Vector (Vector R m) n`.

**Contents:**
- `Matrix R n m` := `Vector (Vector R m) n` (uses stdlib `Vector`)
- Matrix-vector multiplication, matrix-matrix multiplication
- Dot product, norm squared (for `R = Int` and `R = Rat`)
- Row operations (swap, scale, add multiple of one row to another)
- Row reduction (RREF over fields) and span/nullspace machinery:

  ```lean
  /-- Pure data: the result of row-reducing a matrix. -/
  structure RowEchelonData (R : Type) (n m : Nat) where
    rank : Nat
    echelon : Matrix R n m
    transform : Matrix R n n
    pivotCols : Vector (Fin m) rank

  /-- Shared conditions for any echelon form (RREF or HNF). -/
  structure IsEchelonForm (M : Matrix R n m) (D : RowEchelonData R n m) : Prop where
    transform_mul : D.transform * M = D.echelon
    transform_inv : ∃ Tinv : Matrix R n n, Tinv * D.transform = 1
    transform_right_inv : ∃ Tinv : Matrix R n n, D.transform * Tinv = 1
    rank_le_n : D.rank ≤ n
    rank_le_m : D.rank ≤ m
    pivotCols_sorted : ∀ i j, i < j → D.pivotCols[i] < D.pivotCols[j]
    below_pivot_zero : ∀ (i : Fin D.rank) (j : Fin n),
        i.val < j.val → D.echelon[j][D.pivotCols[i]] = 0
    zero_row : ∀ (i : Fin n), D.rank ≤ i.val → D.echelon[i] = 0

  /-- RREF-specific: pivots are 1, everything above is 0. -/
  structure IsRREF (M : Matrix R n m) (D : RowEchelonData R n m)
      extends IsEchelonForm M D : Prop where
    pivot_one : ∀ (i : Fin D.rank), D.echelon[i][D.pivotCols[i]] = 1
    above_pivot_zero : ∀ (i : Fin D.rank) (j : Fin n),
        j.val < i.val → D.echelon[j][D.pivotCols[i]] = 0

  def rref [Field R] [DecidableEq R] (M : Matrix R n m) : RowEchelonData R n m
  theorem rref_isRREF [Field R] [DecidableEq R] (M : Matrix R n m) : IsRREF M (rref M)
  ```

  **Column partition.** The sorted complement of `pivotCols` in
  `Fin m`. Together with `pivotCols` they partition all column
  indices; this decomposition is used by both span and nullspace.

  ```lean
  /-- Sorted complement of pivotCols in Fin m. Requires IsEchelonForm
      because pivotCols_sorted + rank_le_m guarantee distinct pivots. -/
  def IsEchelonForm.freeCols (E : IsEchelonForm M D) :
      Vector (Fin m) (m - D.rank)

  theorem IsEchelonForm.freeCols_sorted (E : IsEchelonForm M D) :
      ∀ i j, i < j → E.freeCols[i] < E.freeCols[j]

  /-- Every column is exclusively a pivot column or a free column. -/
  theorem IsEchelonForm.colPartition (E : IsEchelonForm M D)
      (j : Fin m) :
      (∃ i : Fin D.rank, D.pivotCols[i] = j) ∨
      (∃ k : Fin (m - D.rank), E.freeCols[k] = j)

  theorem IsEchelonForm.colPartition_exclusive (E : IsEchelonForm M D)
      (j : Fin m) :
      ¬((∃ i : Fin D.rank, D.pivotCols[i] = j) ∧
        (∃ k : Fin (m - D.rank), E.freeCols[k] = j))
  ```

  **Span via echelon form.** Given an `IsEchelonForm`, solve for
  coefficients or test membership. Works for both RREF and HNF.

  ```lean
  def IsEchelonForm.spanCoeffs [Field R] [DecidableEq R] (F : IsEchelonForm M D)
      (v : Vector R m) : Option (Vector R n)
  def IsEchelonForm.spanContains [Field R] [DecidableEq R] (F : IsEchelonForm M D)
      (v : Vector R m) : Bool

  /-- Convenience: compute RREF internally. -/
  def Matrix.spanCoeffs [Field R] [DecidableEq R] (M : Matrix R n m) (v : Vector R m) :
      Option (Vector R n)
  def Matrix.spanContains [Field R] [DecidableEq R] (M : Matrix R n m) (v : Vector R m) : Bool
  ```

  **Nullspace** via RREF. Each free variable gives one basis vector.
  The basis-vector formula uses negation (`[Ring R]`) and the proof
  of completeness requires RREF (`[Field R]` for computing RREF).

  ```lean
  /-- Primary definition. Basis vectors as columns of an m × (m - rank) matrix.
      Column k (for free column fₖ):
        row fₖ = 1, row fₗ = 0 for l ≠ k,
        row pᵢ = -echelon[i][fₖ] for each pivot row i. -/
  def IsRREF.nullspaceMatrix [Ring R] (E : IsRREF M D) :
      Matrix R m (m - D.rank)

  /-- Individual basis vectors (columns of nullspaceMatrix). -/
  def IsRREF.nullspace [Ring R] (E : IsRREF M D) :
      Vector (Vector R m) (m - D.rank)

  /-- Convenience: compute RREF internally. -/
  def Matrix.nullspace [Field R] [DecidableEq R] (M : Matrix R n m) :
      Vector (Vector R m) (m - rref_rank)
  ```

- Generic over the coefficient type `R`

**Determinant — definition and computation:**

Define `det` via the Leibniz formula (sum over permutations), over any
`Ring`. (Theorems about `det` will require `CommRing`.)

For computation, provide the Bareiss algorithm (fraction-free Gaussian
elimination) over `Int`. The Bareiss recurrence at step k is:
```
a_{ij}^{(k)} = (a_{kk}^{(k-1)} · a_{ij}^{(k-1)} - a_{ik}^{(k-1)} · a_{kj}^{(k-1)}) / a_{k-1,k-1}^{(k-2)}
```
where `/` is `Int.divExact` (GMP-backed `mpz_divexact`) — the division is
always exact, and the divisibility proof is carried.

**Mathlib-free vs. Mathlib-bridge proof surface.** The following
theorems live exclusively in `hex-matrix-mathlib` and **must not**
be restated, reproven, or specialized inside `hex-matrix`,
regardless of how convenient that would be for a downstream
Mathlib-free consumer:

| Theorem (or theorem family) | Mathlib-free layer obligation |
|---|---|
| `bareiss_eq_det` — any equation of the form `bareiss M = det M` over the Leibniz `det` | forbidden in `hex-matrix` |
| `det_eq` — `Hex.det M = Matrix.det (matrixEquiv M)` | forbidden in `hex-matrix` |
| Desnanot–Jacobi in any form (unscaled, scaled, bordered-minor) that connects `Hex.det` of submatrices through an adjugate identity | forbidden in `hex-matrix` |
| `NonzeroBareissPivots`, `BareissNoPivotInvariant`, and the no-pivot bordered-minor invariant proof chain culminating in `bareissNoPivot_eq_det` | forbidden in `hex-matrix` |

A Mathlib-free consumer that *appears to require* a theorem on
this list is the failure mode caught by
[PLAN/Conventions.md §Library placement is a hard precondition
question 2](https://github.com/kim-em/hex-dev/blob/main/PLAN/Conventions.md#library-placement-is-a-hard-precondition). The repair is to relocate
the consumer's bridging theorem to the sibling `*-mathlib` layer
(or to redesign the consumer's proof surface so it does not need
to connect Hex computation to Leibniz `det` at the Mathlib-free
layer at all). It is **not** to manufacture a Mathlib-free proof
of the listed theorem.

Row-operation lemmas (`det_rowSwap`, `det_rowScale`, `det_rowAdd`)
and equalities purely between Hex-local definitions remain in
`hex-matrix` and are unaffected by this list.

**Proof path governs placement, not just statement.** A theorem
whose *statement* is purely Hex-local (e.g. `bareiss (rowAdd M
i j c) = bareiss M`, with `det` nowhere mentioned) still belongs in
`hex-matrix-mathlib` if its only realistic Mathlib-free proof
requires re-deriving an entry from the forbidden list above —
re-deriving Desnanot–Jacobi by hand, restating the no-pivot
bordered-minor invariant under a renamed lemma, or threading
`bareiss_eq_det` through twice while hiding it behind a wrapper.
The shortest-path test in
[PLAN/Conventions.md §Library placement is a hard precondition
question 2](https://github.com/kim-em/hex-dev/blob/main/PLAN/Conventions.md#library-placement-is-a-hard-precondition) governs **proof
obligations**, not statement surface. A Hex-local statement with a
bridge-only proof is the same SPEC violation as a bridge-typed
statement, dressed up.

A Hex-local `bareiss → bareiss` equation whose proof inducts
directly on the executable Bareiss recurrence belongs in
`hex-matrix-mathlib`, not `hex-matrix`: the induction's correctness
rests on Desnanot–Jacobi (or its `Int`-narrowed shadow), and
restating that locally re-derives a forbidden theorem under a
different name. When a Mathlib-free consumer appears to need such
an equation, relocate the consumer to the bridge layer rather
than inlining the derivation.

**Proof that `bareiss M = det M`:** Via the bordered-minor invariant.
Define `μ(k; i, j) := det M[rows 0..k-1 ∪ {i} | cols 0..k-1 ∪ {j}]`.
The invariant `a^{(k)}_{ij} = μ(k; i, j)` holds by induction, where
the induction step is the Desnanot–Jacobi identity:
```
μ(k+1; i, j) · μ(k-1; k-1, k-1)
  = μ(k; k, k) · μ(k; i, j) − μ(k; i, k) · μ(k; k, j)
```
for `i, j ≥ k+1`, with `μ(-1; -1, -1) := 1`. At `k = n-1` this
gives `det M`. Exact division follows: `μ(k+1; i, j)` is an integer
whenever the previous pivot `μ(k-1; k-1, k-1) ≠ 0`.

Do not reprove Desnanot–Jacobi locally — track
https://github.com/leanprover-community/mathlib4/pull/37716
(`Mathlib.LinearAlgebra.Matrix.Determinant.DesnanotJacobi`). If merged,
import it; otherwise prove locally using Mathlib's `Matrix.adjugate`.

Implementation split:
1. `bareissNoPivot_eq_det`: under `NonzeroBareissPivots M`, prove via
   the invariant + Desnanot–Jacobi.
2. `bareissDet_eq_det`: public API with row pivoting. If pivot search
   fails at step k, prove `det M = 0`; otherwise compose row swaps
   into a permutation, apply the no-pivot theorem, use `det_rowSwap`
   for sign.

The proof lives in hex-matrix-mathlib. Row-operation lemmas
(`det_rowSwap`, `det_rowScale`, `det_rowAdd`) remain in hex-matrix
for RREF and pivot sign tracking.

**Key properties:**
- `det_one : det 1 = 1`
- `det_rowSwap : i ≠ j → det (rowSwap M i j) = -det M`
- `det_rowScale : det (rowScale M i c) = c * det M`
- `det_rowAdd : i ≠ j → det (rowAdd M i j c) = det M`
- `bareiss_eq_det : bareiss M = det M`
- `spanCoeffs_sound : E.spanCoeffs v = some c → rowCombination M c = v`
- `spanCoeffs_complete : (∃ c, rowCombination M c = v) → (E.spanCoeffs v).isSome`
- `spanContains_iff : E.spanContains v = true ↔ ∃ c, rowCombination M c = v`
- `transform_mul_inv : ∃ Tinv, D.transform * Tinv = 1`
- `freeCols_sorted`, `colPartition`, `colPartition_exclusive` (see column partition above)
- `pivotCols_injective`, `freeCols_injective` (from `_sorted`)
- `pivotCols_disjoint_freeCols` (from `colPartition_exclusive`)
- Nullspace soundness and completeness (see below)

**Nullspace correctness:**

```lean
theorem nullspace_sound [Ring R] (E : IsRREF M D) (k : Fin (m - D.rank)) :
    M * E.nullspace[k] = 0

theorem nullspace_complete [Field R] (E : IsRREF M D) (v : Vector R m) :
    M * v = 0 → ∃ c : Vector R (m - D.rank), E.nullspaceMatrix * c = v
```

(`nullspace_rank` is now definitional: `E.nullspace` has type
`Vector _ (m - D.rank)`, so its length is `m - D.rank` by construction.)

Proof strategy for `nullspace_sound`: verify `D.echelon * bₖ = 0`
directly from the basis-vector formula and RREF properties, then
use `transform_inv` to obtain `Tinv` with `Tinv * D.transform = 1`,
so `M = Tinv * D.echelon` and `M * bₖ = Tinv * (D.echelon * bₖ) = 0`.

Proof strategy for `nullspace_complete`:

1. **Push through transform.** `M * v = 0` implies
   `D.echelon * v = 0` via `transform_mul` and associativity.

2. **Construct witness.** Define `cₖ := v[E.freeCols[k]]` for each
   `k : Fin (m - D.rank)`.

3. **Verify entry by entry.** Split `j : Fin m` using `colPartition`:
   - *Free column* `j = freeCols[l]`: the sum telescopes to
     `cₗ · 1 = v[freeCols[l]]` by the identity/zero structure of
     the basis vectors on free columns.
   - *Pivot column* `j = pivotCols[i]`: row `i` of
     `D.echelon * v = 0` gives (using `pivot_one`,
     `above_pivot_zero`, `below_pivot_zero`, `zero_row`):
     `v[pivotCols[i]] = -∑ₖ D.echelon[i][freeCols[k]] · v[freeCols[k]]`,
     which matches `∑ₖ cₖ · bₖ[pivotCols[i]]` by the basis-vector
     definition `bₖ[pᵢ] = -D.echelon[i][freeCols[k]]`.

4. **Package.** The entry-wise equality gives
   `E.nullspaceMatrix * c = v`.

## External comparators

| Comparator | Class | Scope |
|---|---|---|
| FLINT `fmpz_mat_det` via python-flint | informational | determinant-surface bench targets only (`runBareissDet` and equivalents) |

FLINT's `fmpz_mat_det` is a structurally distinct reference for
integer matrix determinant: FLINT uses multimodular reduction
(determinant modulo many small primes, then CRT) which has
different asymptotic and constant-factor profile from Bareiss
fraction-free elimination. The comparator is `informational`:
the ratio is recorded for orientation but is not a Phase-4 gate.
Wired via a persistent-subprocess Python driver per
[the benchmarking spec's "External comparators" section](https://github.com/kim-em/hex-dev/blob/main/SPEC/benchmarking.md#external-comparators).

The library's other Phase-4 surfaces (matrix multiplication, row
operations, transposition, slicing) have no external comparator
named. They declare absence with the **structural-layer** reason
per [the benchmarking spec's "Comparator naming" section](https://github.com/kim-em/hex-dev/blob/main/SPEC/benchmarking.md#comparator-naming): those surfaces
are GMP-backed `Int` arithmetic on `Vector` / `Array` primitives,
and the determinant comparator covers the only matrix-specific
algorithmic surface where an external reference adds meaningful
orientation.

Structured metadata in the project's [`libraries.yml`](https://github.com/kim-em/hex-dev/blob/main/libraries.yml) under `HexMatrix.phase4.comparators`.
