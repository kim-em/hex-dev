# hex-row-reduce-mathlib (depends on hex-row-reduce + hex-matrix-mathlib + Mathlib)

## Correspondence-only classification

This library is a `correspondence-only-layer`.

Computational conformance owner: `HexRowReduce`
Computational performance owner: `HexRowReduce`

Mathlib bridge for `hex-row-reduce`: connects our computable RREF / rank / span /
nullspace machinery to Mathlib's noncomputable linear-algebra definitions, via
the base `matrixEquiv` from `hex-matrix-mathlib`.

**Rank:** Our `RowEchelonData.rank` (computed via RREF) agrees with Mathlib's
`Matrix.rank` (noncomputable, `finrank R (LinearMap.range M.mulVecLin)`):
```lean
theorem rank_eq [Field R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsRowReduced M D) :
    D.rank = _root_.Matrix.rank (matrixEquiv M)
```

This is deliberately a theorem about a reduced row-echelon witness, not an
arbitrary `IsEchelonForm`: the proof obtains the kernel dimension from the
computed nullspace basis, whose completeness and independence require
`IsRowReduced`. The bridge theorem uses Mathlib's `Field`; the executable
row-reduction, span, and nullspace APIs in `HexRowReduce` use
`Lean.Grind.Field` (and `DecidableEq` where computation requires it).

**Nullspace:** Our computed nullspace basis spans the same submodule as
`LinearMap.ker (Matrix.mulVecLin (matrixEquiv M))`.

**Span:** Our `IsEchelonForm.spanContains` agrees with membership in
`Submodule.span R (Set.range M.row)`.

This makes our row-reduction computations computable witnesses for Mathlib's
noncomputable rank/kernel/span definitions.
