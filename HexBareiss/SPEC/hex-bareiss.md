# hex-bareiss (depends on hex-determinant, hex-matrix)

The executable Bareiss determinant (fraction-free Gaussian elimination) over
`Int`, plus the bordered-minor support its correctness development relies on.

**Algorithm.** The Bareiss recurrence at step k is:
```
a_{ij}^{(k)} = (a_{kk}^{(k-1)} · a_{ij}^{(k-1)} - a_{ik}^{(k-1)} · a_{kj}^{(k-1)}) / a_{k-1,k-1}^{(k-2)}
```
where `/` is `Int.divExact` (GMP-backed `mpz_divexact`) — the division is always
exact, and the divisibility proof is carried. Public API performs row pivoting;
`bareissData` records the determinant and the row-swap count.

**Mathlib-free vs. Mathlib-bridge proof surface.** The following theorems live
exclusively in the `*-mathlib` bridge layer and **must not** be restated,
reproven, or specialized inside `hex-bareiss`, regardless of how convenient that
would be for a downstream Mathlib-free consumer:

| Theorem (or theorem family) | Mathlib-free layer obligation |
|---|---|
| `bareiss_eq_det` — any equation of the form `bareiss M = det M` over the Leibniz `det` | forbidden in `hex-bareiss` |
| `det_eq` — `Hex.det M = Matrix.det (matrixEquiv M)` | forbidden in `hex-bareiss` |
| Desnanot–Jacobi in any form (unscaled, scaled, bordered-minor) that connects `Hex.det` of submatrices through an adjugate identity | forbidden in `hex-bareiss` |
| `NonzeroBareissPivots`, `BareissNoPivotInvariant`, and the no-pivot bordered-minor invariant proof chain culminating in `bareissNoPivot_eq_det` | forbidden in `hex-bareiss` |

A Mathlib-free consumer that *appears to require* a theorem on this list is the
failure mode caught by
[PLAN/Conventions.md §Library placement is a hard precondition question 2](https://github.com/kim-em/hex-dev/blob/main/PLAN/Conventions.md#library-placement-is-a-hard-precondition).
The repair is to relocate the consumer's bridging theorem to the sibling
`*-mathlib` layer (or to redesign the consumer's proof surface), **not** to
manufacture a Mathlib-free proof of the listed theorem.

Row-operation lemmas (`det_rowSwap`, `det_rowScale`, `det_rowAdd`, in
`hex-determinant`) and equalities purely between Hex-local definitions are
unaffected by this list.

**Proof path governs placement, not just statement.** A theorem whose
*statement* is purely Hex-local (e.g. `bareiss (rowAdd M i j c) = bareiss M`,
with `det` nowhere mentioned) still belongs in the bridge layer if its only
realistic Mathlib-free proof requires re-deriving an entry from the forbidden
list above. The shortest-path test in
[PLAN/Conventions.md §Library placement is a hard precondition question 2](https://github.com/kim-em/hex-dev/blob/main/PLAN/Conventions.md#library-placement-is-a-hard-precondition)
governs **proof obligations**, not statement surface.

**Proof that `bareiss M = det M`:** Via the bordered-minor invariant. Define
`μ(k; i, j) := det M[rows 0..k-1 ∪ {i} | cols 0..k-1 ∪ {j}]`. The invariant
`a^{(k)}_{ij} = μ(k; i, j)` holds by induction, where the induction step is the
Desnanot–Jacobi identity:
```
μ(k+1; i, j) · μ(k-1; k-1, k-1)
  = μ(k; k, k) · μ(k; i, j) − μ(k; i, k) · μ(k; k, j)
```
for `i, j ≥ k+1`, with `μ(-1; -1, -1) := 1`. At `k = n-1` this gives `det M`.
Exact division follows: `μ(k+1; i, j)` is an integer whenever the previous pivot
`μ(k-1; k-1, k-1) ≠ 0`.

Do not reprove Desnanot–Jacobi locally — track
https://github.com/leanprover-community/mathlib4/pull/37716
(`Mathlib.LinearAlgebra.Matrix.Determinant.DesnanotJacobi`). If merged, import
it; otherwise prove using Mathlib's `Matrix.adjugate`.

Implementation split (the proofs live in the Mathlib bridge layer):
1. `bareissNoPivot_eq_det`: under `NonzeroBareissPivots M`, prove via the
   invariant + Desnanot–Jacobi.
2. `bareissDet_eq_det`: public API with row pivoting. If pivot search fails at
   step k, prove `det M = 0`; otherwise compose row swaps into a permutation,
   apply the no-pivot theorem, use `det_rowSwap` for sign.

## External comparators

| Comparator | Class | Scope |
|---|---|---|
| FLINT `fmpz_mat_det` via python-flint | informational | the Bareiss determinant bench targets (`runBareissDet` and the paired FLINT rungs) |

FLINT's `fmpz_mat_det` is a structurally distinct reference for integer matrix
determinant: FLINT uses multimodular reduction (determinant modulo many small
primes, then CRT), with a different asymptotic and constant-factor profile from
Bareiss fraction-free elimination. The comparator is `informational`: the ratio
is recorded for orientation but is not a Phase-4 gate. Wired via a
persistent-subprocess Python driver per
[the benchmarking spec's "External comparators" section](https://github.com/kim-em/hex-dev/blob/main/SPEC/benchmarking.md#external-comparators).

Structured metadata in the project
[`libraries.yml`](https://github.com/kim-em/hex-dev/blob/main/libraries.yml)
under `HexBareiss.phase4.comparators`. See
`reports/hex-bareiss-performance.md` for the comparator ratio ladder.
