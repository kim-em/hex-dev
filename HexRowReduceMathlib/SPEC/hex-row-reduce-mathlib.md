# hex-row-reduce-mathlib (depends on hex-row-reduce + hex-matrix-mathlib + Mathlib)

Mathlib bridge for `hex-row-reduce`: connects our computable RREF / rank / span /
nullspace machinery to Mathlib's noncomputable linear-algebra definitions, via
the base `matrixEquiv` from `hex-matrix-mathlib`.

**Rank:** Our `RowEchelonData.rank` (computed via RREF) agrees with Mathlib's
`Matrix.rank` (noncomputable, `finrank R (LinearMap.range M.mulVecLin)`):
```lean
theorem rank_eq (M : Hex.Matrix R n m)
    (D : RowEchelonData R n m) (E : IsEchelonForm M D) :
    D.rank = Matrix.rank (matrixEquiv M)
```

**Nullspace:** Our computed nullspace basis spans the same submodule as
`LinearMap.ker (Matrix.mulVecLin (matrixEquiv M))`.

**Span:** Our `IsEchelonForm.spanContains` agrees with membership in
`Submodule.span R (Set.range M.row)`.

This makes our row-reduction computations computable witnesses for Mathlib's
noncomputable rank/kernel/span definitions.
