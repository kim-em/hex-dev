# hex-row-reduce-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-row-reduce-mathlib` is the Mathlib bridge for
[`hex-row-reduce`](https://github.com/kim-em/hex-row-reduce). It proves that
the executable row reduction, rank, row span, and nullspace agree with
Mathlib's noncomputable linear-algebra definitions. It depends on
[`hex-row-reduce`](https://github.com/kim-em/hex-row-reduce),
[`hex-matrix-mathlib`](https://github.com/kim-em/hex-matrix-mathlib), and
Mathlib.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-row-reduce-mathlib"
git = "https://github.com/kim-em/hex-row-reduce-mathlib.git"
rev = "main"
```

```lean
import HexRowReduceMathlib

open HexMatrixMathlib

-- The computed rank agrees with Mathlib's `Matrix.rank`.
#check @rank_eq

-- The computed nullspace basis spans exactly the kernel of `mulVecLin`.
#check @nullspace_span_eq_ker

-- The executable span-membership test agrees with `Submodule.span`.
#check @spanContains_iff_mem_span
```

# Functionality

The library transports the executable row-reduction data of an
`Hex.Matrix R n m` to Mathlib's function-based matrix `matrixEquiv M`, then
states the correspondence theorems:

- `vectorEquiv_rowCombination`: an executable row combination transports to
  Mathlib's `Fintype.linearCombination` over the rows of `matrixEquiv M`;
- `spanCoeffs_eq_linearCombination` and `spanContains_iff_mem_span`: the
  executable span witnesses and the decidable span-membership test agree with
  `Submodule.span`;
- `rowReduce_echelon_row_mem_span` and
  `rowReduce_mem_span_echelon_of_mem_span`: row reduction preserves the row
  span, in both directions;
- `nullspace_mem_ker` and `nullspace_span_eq_ker`: the computed nullspace
  basis lies in, and spans, `LinearMap.ker (Matrix.mulVecLin (matrixEquiv M))`;
- `rank_eq`: the rank from row reduction equals `Matrix.rank (matrixEquiv M)`.

# Verification

Over a `Field R`, the correspondence is fully proven. The computed rank,
row span, and nullspace are computable witnesses for Mathlib's noncomputable
`Matrix.rank`, `Submodule.span`, and `LinearMap.ker` definitions.

Rank, `rank_eq`:

```lean
theorem rank_eq [Field R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsRowReduced M D) :
    D.rank = _root_.Matrix.rank (matrixEquiv M)
```

Nullspace, `nullspace_span_eq_ker`:

```lean
theorem nullspace_span_eq_ker [Field R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsRowReduced M D) :
    Submodule.span R (Set.range fun k : Fin (m - D.rank) => vectorEquiv (E.nullspace.get k)) =
      LinearMap.ker (_root_.Matrix.mulVecLin (matrixEquiv M))
```

Span, `spanContains_iff_mem_span`:

```lean
theorem spanContains_iff_mem_span [Field R] [DecidableEq R]
    {M : Hex.Matrix R n m} {D : Hex.Matrix.RowEchelonData R n m}
    (E : Hex.Matrix.IsRowReduced M D) (v : Vector R m) :
    E.toIsEchelonForm.spanContains v = true ↔
      vectorEquiv v ∈ Submodule.span R (Set.range (_root_.Matrix.row (matrixEquiv M)))
```

The executable row reduction itself lives in
[`hex-row-reduce`](https://github.com/kim-em/hex-row-reduce).

# Reference manual

The hex reference manual covers this library and its computational base at
<https://kim-em.github.io/hex-dev/find/?domain=Verso.Genre.Manual.section&name=hex-row-reduce>.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want, and
leave the implementation to the maintainer.
