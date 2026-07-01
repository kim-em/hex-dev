# hex-matrix

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-matrix` provides dense matrices, represented as `Vector (Vector R m) n`
and generic over the coefficient type `R`. This library has no dependencies.
See [`hex-matrix-mathlib`](https://github.com/leanprover/hex-matrix-mathlib) for
the correspondence with Mathlib's types and theory.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-matrix"
git = "https://github.com/leanprover/hex-matrix.git"
rev = "main"
```

```lean
import HexMatrix

open Hex

-- Build a matrix from an entry function, or write one out explicitly.
def A : Matrix Int 2 3 := Matrix.ofFn fun i j => (i + j : Int)
def B : Matrix Int 3 2 := #m[1, 2; 3, 4; 5, 6]

#eval A * B                        -- 2×2 matrix product
#eval Matrix.transpose A           -- 3×2 transpose
#eval Matrix.gramMatrix A          -- A * Aᵀ
#eval Matrix.mulVec A (Vector.ofFn fun j => (j + 1 : Int))

-- Elementary row operations.
#eval Matrix.rowSwap A 0 1
#eval Matrix.rowScale A 0 5
#eval Matrix.identity (R := Int) 3 -- the 3×3 identity
```

# Functionality

Dense `n × m` matrices over an arbitrary coefficient type:

- constructors and accessors: `ofFn`, `row`, `col`, `setRow`, `setCol`,
  `transpose`, the zero and identity matrices;
- arithmetic: vector dot product and norm-squared, matrix-vector and
  matrix-matrix multiplication (also via `*`);
- elementary row operations `rowSwap`, `rowScale`, `rowAdd`, `rowMoveUp`
  and the column analogues `colAdd` / `colAddRight`;
- submatrix / leading-submatrix slicing and the Gram matrix `M * Mᵀ`.

Row reduction ([`hex-row-reduce`](https://github.com/leanprover/hex-row-reduce)),
the Leibniz determinant ([`hex-determinant`](https://github.com/leanprover/hex-determinant)),
and the Bareiss algorithm ([`hex-bareiss`](https://github.com/leanprover/hex-bareiss))
build on it.

# Verification

The elementary operations and matrix algebra carry their algebraic
identities: entrywise characterizations of every operation, the identity
matrix acting as a left and right multiplicative identity, involutivity of
`transpose`, `gramMatrix M = M * Mᵀ`, and the involutivity, multiplicative,
and inverse-preservation lemmas for the elementary operations.

The `Semiring` / `Ring` structure and the equivalence with Mathlib's
`Matrix`, which let you transfer Mathlib's linear-algebra results, live in
[`hex-matrix-mathlib`](https://github.com/leanprover/hex-matrix-mathlib).

# Reference manual

The hex reference manual covers this library at
<https://kim-em.github.io/hex-dev/find/?domain=Verso.Genre.Manual.section&name=hex-matrix>.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want, and
leave the implementation to the maintainer.
