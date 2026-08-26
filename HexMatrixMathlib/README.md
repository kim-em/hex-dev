# hex-matrix-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-matrix-mathlib` is the Mathlib bridge for
[`hex-matrix`](https://github.com/leanprover/hex-matrix). It identifies the
executable dense matrices with Mathlib's function-based `Matrix`, so that
Mathlib's linear-algebra results transfer to the computable representation.
This library depends on Mathlib and on
[`hex-matrix`](https://github.com/leanprover/hex-matrix).

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-matrix-mathlib"
git = "https://github.com/leanprover/hex-matrix-mathlib.git"
rev = "main"
```

```lean
import HexMatrixMathlib

open Hex HexMatrixMathlib

-- Every executable matrix corresponds to a Mathlib matrix with the same entries.
#check @matrixEquiv      -- Hex.Matrix R n m ≃ Matrix (Fin n) (Fin m) R
#check @matrixEquiv_apply -- matrixEquiv M i j = M[i][j]

-- Elementary row operations become Mathlib's elementary matrices.
#check @matrixEquiv_rowSwap -- left multiply by Matrix.swap
#check @matrixEquiv_rowAdd  -- left multiply by Matrix.transvection

-- The executable arithmetic is Mathlib's algebraic tower.
#check @matrixRingEquiv  -- Hex.Matrix R n n ≃+* Matrix (Fin n) (Fin n) R
```

# Functionality

The proof-facing API connecting the two matrix worlds:

- the equivalence `matrixEquiv : Hex.Matrix R n m ≃ Matrix (Fin n) (Fin m) R`
  and its companion `vectorEquiv : Vector R n ≃ (Fin n → R)`;
- the algebraic instances on `Hex.Matrix` whose operations are the executable
  ones: `AddCommMonoid`, `AddCommGroup`, `Module`, `instSemiring`, `instRing`,
  and `instAlgebra`, transported along `matrixEquiv`;
- the bundled upgrades `matrixAddEquiv`, `matrixLinearEquiv`, `matrixRingEquiv`,
  and `matrixAlgEquiv`;
- the row-operation dictionary `matrixEquiv_rowSwap`, `matrixEquiv_rowScale`,
  and `matrixEquiv_rowAdd`;
- transfer lemmas for the container API: `matrixEquiv_transpose`,
  `matrixEquiv_setRow`, `matrixEquiv_setCol`, `matrixEquiv_gramMatrix`,
  `matrixEquiv_principalSubmatrix`, and the matrix-vector product
  `vectorEquiv_mulVec`.

# Verification

The correspondence is fully proven. The algebraic instances are transported
across `matrixEquiv`, so their laws are Mathlib's; the `@[simp, grind]`
transfer lemmas (`matrixEquiv_add`, `matrixEquiv_mul`, `matrixEquiv_one`,
`matrixEquiv_smul`, and the rest) let `simp` and `grind` rewrite between the
two representations.

The headline equivalence sends each matrix to the Mathlib matrix with the
same entries:

```lean
def matrixEquiv : Hex.Matrix R n m ≃ Matrix (Fin n) (Fin m) R
```

```lean
theorem matrixEquiv_apply (M : Hex.Matrix R n m) (i : Fin n) (j : Fin m) :
    matrixEquiv M i j = M[i][j]
```

The elementary row operations correspond to Mathlib's elementary matrices.
A swap is left multiplication by the permutation matrix `Matrix.swap`:

```lean
theorem matrixEquiv_rowSwap (M : Hex.Matrix R n m) (i j : Fin n) :
    matrixEquiv (Hex.Matrix.rowSwap M i j) = Matrix.swap R i j * matrixEquiv M
```

A row addition is left multiplication by `Matrix.transvection`:

```lean
theorem matrixEquiv_rowAdd (M : Hex.Matrix R n m) (src dst : Fin n) (c : R) :
    matrixEquiv (Hex.Matrix.rowAdd M src dst c) =
      Matrix.transvection dst src c * matrixEquiv M
```

The matrix-vector product transports to Mathlib's `Matrix.mulVec`:

```lean
theorem vectorEquiv_mulVec [Semiring R] (M : Hex.Matrix R n m) (v : Vector R m) :
    vectorEquiv (M * v) = (matrixEquiv M).mulVec (vectorEquiv v)
```

The executable matrices and their operations live in
[`hex-matrix`](https://github.com/leanprover/hex-matrix). The determinant, row
reduction, and Bareiss correspondences build on this base in their own bridge
libraries.

# Reference manual

The Mathlib correspondence section of the hex reference manual covers this library at
<https://kim-em.github.io/hex-dev/find/?domain=Verso.Genre.Manual.section&name=hex-matrix-mathlib>.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want, and
leave the implementation to the maintainer.
