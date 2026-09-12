# hex-row-reduce

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-row-reduce` provides Gauss-Jordan row reduction to reduced row echelon
form over a field, together with row-span and nullspace computations,
two-sided field inversion, and complete linear solving. This library depends only on [`hex-matrix`](https://github.com/leanprover/hex-matrix).
See [`hex-row-reduce-mathlib`](https://github.com/leanprover/hex-row-reduce-mathlib)
for the correspondence with Mathlib's types and theory.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-row-reduce"
git = "https://github.com/leanprover/hex-row-reduce.git"
rev = "main"
```

```lean
import HexRowReduce

open Hex

-- A 2×3 matrix over the rationals with a dependent second row.
def M : Matrix Rat 2 3 := Matrix.ofFn fun i j => (i + 1) * (j + 1 : Rat)

#eval (Matrix.rowReduce M).rank          -- 1, the rank
#eval (Matrix.rowReduce M).echelon       -- the reduced row echelon form
#eval (Matrix.rowReduce M).transform     -- T with T * M = echelon

#eval Matrix.spanContains M (Vector.ofFn fun j => (j + 1 : Rat))  -- true
#eval Matrix.spanCoeffs M (Vector.ofFn fun j => (j + 1 : Rat))    -- the coefficients

#eval Matrix.nullspace M                 -- a basis for the nullspace
```

# Functionality

- `rowReduce`: Gauss-Jordan reduction of a matrix over a field, returning the
  rank, the reduced row echelon form, the invertible transform matrix, and the
  pivot columns;
- `rowReduce_rank`: the rank read off the reduction;
- `spanCoeffs` and `spanContains`: solve for row-combination coefficients of a
  vector, or test row-span membership;
- `rowCombination`: the linear combination of the rows of a matrix;
- `nullspace` and `nullspaceBasisMatrix`: a basis for the nullspace, one vector
  per free column, as a vector of vectors or as a matrix of columns;
- `inverse? A`: returns a two-sided inverse exactly when a square matrix has
  full rank, including the empty identity at dimension zero;
- `solve A b`: returns `.ok (x₀, N)` describing every solution as `x₀ + N * c`,
  with unique coefficients `c`, or `.error y` with `vecMul y A = 0` and
  `Vector.dotProduct y b ≠ 0`;
- `solve? A b`: the option view of `solve`, forgetting the error witness.

Inverse and solve use `Lean.Grind.Field` and decidable equality. They share
the coefficient matrix reduction with the transform and basis construction.
Failure means singularity for inverse, and inconsistency for solve; singular
systems can have many solutions. There is no resource-failure return.

The main contracts are `inverse?_spec`, `inverse?_isSome`, `solve?_spec`,
`solve?_isSome`, `solve_error`, `solve?_none_witness`, and `solve?_unique`.
`solve?_free` states that the particular solution has zero free coordinates.
The conformance suite exercises `Rat`, prime `ZMod64`, and `RationalFn Rat`,
including empty and rectangular shapes.

# Relationship to domain rank certificates

The hex-rank certificate API works over domains and checks a numerator `adj`
and nonzero denominator for the inverse of a selected nonsingular minor.
Division belongs in a fraction field unless the denominator is a unit; an
invertible rational matrix with integer entries need not have an integer
inverse. If the selected full-size minor is `B = P * A * Q`, undo the
selections to obtain `A⁻¹ = Q * (denom⁻¹ • adj) * P`. The certificate numerator
and denominator need not be the literal adjugate and determinant.

`inverse?` works directly over a field and returns the inverse in the original
indexing. The two answers agree over a common field by uniqueness of a
two-sided inverse. Neither library depends on the other.

# Verification

Over a field the reduction is fully proven. The headline theorem states that
`rowReduce` always meets the reduced-row-echelon contract `IsRowReduced` (pivots
sorted and equal to 1, all other pivot-column entries zero, trailing rows zero,
and an invertible transform with `transform * M = echelon`):

```lean
theorem rowReduce_isRowReduced (M : Matrix R n m) : IsRowReduced M (rowReduce M)
```

The row-span wrappers are sound, with `spanCoeffs_sound`:

```lean
theorem spanCoeffs_sound [Lean.Grind.Field R] [DecidableEq R]
    (M : Matrix R n m) (v : Vector R m) (c : Vector R n) :
    spanCoeffs M v = some c → rowCombination M c = v
```

The nullspace basis is both sound and complete, `nullspace_sound` and
`nullspace_complete`:

```lean
theorem nullspace_sound [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m)
    (k : Fin (m - rowReduce_rank M)) :
    M * (nullspace M).get k = 0

theorem nullspace_complete [Lean.Grind.Field R] [DecidableEq R] (M : Matrix R n m)
    (v : Vector R m) :
    M * v = 0 → ∃ c : Vector R (m - rowReduce_rank M), nullspaceBasisMatrix M * c = v
```

The identification with Mathlib's linear-algebra theory lives in
[`hex-row-reduce-mathlib`](https://github.com/leanprover/hex-row-reduce-mathlib).

# Reference manual

The hex reference manual covers this library at
<https://kim-em.github.io/hex-dev/find/?domain=Verso.Genre.Manual.section&name=hex-row-reduce>.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want, and
leave the implementation to the maintainer.
