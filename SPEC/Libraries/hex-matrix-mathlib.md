# hex-matrix-mathlib (depends on hex-matrix + Mathlib)

Proves that our matrix type and operations correspond to Mathlib's
abstract linear algebra.

Mathlib has no RREF, but does have `Matrix.transvection` (elementary
row operations), `TransvectionStruct`, and a `Pivot` namespace that
reduces matrices to diagonal form via transvections. Mathlib's rank,
kernel, and span are noncomputable (cardinals, infima over submodules).
This bridge connects our computable versions to those definitions.

**Matrix equivalence:**
```lean
def matrixEquiv :
    Hex.Matrix R n m ≃ Matrix (Fin n) (Fin m) R
```

**Row operations correspond to Mathlib transvections:**
Our `rowAdd M i j c` is left-multiplication by
`Matrix.transvection i j c`. Our `rowSwap` and `rowScale` correspond
to Mathlib's `Equiv.swap` and diagonal matrices.

**Determinant:**
```lean
theorem det_eq (M : Hex.Matrix R n n) :
    Hex.det M = Matrix.det (matrixEquiv M)
```

**Rank:** Our `RowEchelonData.rank` (computed via RREF) agrees with
Mathlib's `Matrix.rank` (noncomputable, defined as
`finrank R (LinearMap.range M.mulVecLin)`).
```lean
theorem rank_eq (M : Hex.Matrix R n m)
    (D : RowEchelonData R n m) (E : IsEchelonForm M D) :
    D.rank = Matrix.rank (matrixEquiv M)
```

**Nullspace:** Our computed nullspace basis spans the same submodule
as `LinearMap.ker (Matrix.mulVecLin (matrixEquiv M))`.

**Span:** Our `IsEchelonForm.spanContains` agrees with membership in
`Submodule.span R (Set.range M.row)`.

This means Mathlib theorems (Cramer's rule, Cayley-Hamilton,
rank-nullity, `diagonal_transvection_induction`) transfer to our
matrices, and our computations give computable witnesses for
Mathlib's noncomputable definitions.
