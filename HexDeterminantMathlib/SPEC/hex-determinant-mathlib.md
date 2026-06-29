# hex-determinant-mathlib (depends on hex-determinant + hex-bareiss + hex-matrix-mathlib + Mathlib)

Mathlib bridge for `hex-determinant`: proves that our executable Leibniz
determinant corresponds to Mathlib's `Matrix.det`, and assembles the
permutation-sign transport and the four-row / double-row Plücker and
Desnanot-Jacobi identities used by the Bareiss correctness proof.

**Determinant correspondence:**
```lean
theorem det_eq (M : Hex.Matrix R n n) :
    Hex.det M = Matrix.det (matrixEquiv M)
```

**Internal structure:** the permutation-sign bridge and ordered transport
helpers (`CoreTransport`), the four-row / double-row Plücker and Desnanot-Jacobi
assembly (`CorePlucker`, `DesnanotJacobi`), re-exported through `Core`. The
transport layer imports the executable `hex-bareiss` and `hex-determinant` cores
so the bordered-minor invariant can be stated against the executable Bareiss
recurrence; the `bareiss = det` headline theorems live in `hex-bareiss-mathlib`.

Through `det_eq`, Mathlib determinant theorems (Cramer's rule, Cauchy-Binet,
adjugate identities) transfer to our executable determinant.
