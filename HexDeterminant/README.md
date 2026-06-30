# hex-determinant

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-determinant` provides the determinant of a dense square matrix via the
Leibniz formula, together with the cofactor and adjugate theory. This library
depends only on [`hex-matrix`](https://github.com/kim-em/hex-matrix). See
[`hex-determinant-mathlib`](https://github.com/kim-em/hex-determinant-mathlib)
for the correspondence with Mathlib's types and theory.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-determinant"
git = "https://github.com/kim-em/hex-determinant.git"
rev = "main"
```

```lean
import HexDeterminant

open Hex

def M : Matrix Int 3 3 := Matrix.ofFn fun i j => if i = j then (2 : Int) else 1

#eval Matrix.det M                       -- 4, via the Leibniz formula
#eval Matrix.det (1 : Matrix Int 4 4)    -- 1

-- The determinant tracks elementary row operations.
#eval Matrix.det (Matrix.rowSwap M 0 1)  -- -4, negated

-- Cofactor and adjugate theory is executable too.
#eval Matrix.cofactor M 0 0
#eval Matrix.adjugate M
```

# Functionality

- `det`: the determinant via the Leibniz formula (signed sum over
  permutations), over any `Ring`;
- the determinant of elementary row and column operations;
- cofactor expansion: `deleteRowCol`, `cofactorSign`, `cofactor`, and the
  Laplace expansion along a row or column;
- the adjugate matrix and the column-tuple (Cauchy-Binet) expansion.

# Verification

Over a `CommRing` the determinant's behaviour is fully proven, starting with
`det_one` and the row-operation laws `det_rowSwap`, `det_rowScale`, and
`det_rowAdd`.

The headline theorem for each of the remaining results (with
`[Lean.Grind.CommRing R]` throughout):

Column linearity, `det_setCol_add`:

```lean
theorem det_setCol_add (M : Matrix R n n) (dst : Fin n) (v w : Fin n → R) :
    det (setCol M dst (fun r => v r + w r)) =
      det (setCol M dst v) + det (setCol M dst w)
```

Laplace cofactor expansion along a row, `det_eq_foldl_laplace_row`:

```lean
theorem det_eq_foldl_laplace_row (M : Matrix R (n + 1) (n + 1)) (row : Fin (n + 1)) :
    det M =
      (List.finRange (n + 1)).foldl
        (fun acc col => acc + M[row][col] * cofactor M row col) 0
```

We prove the Cauchy-Binet column-tuple product formula (Gram form) as
`det_gramMatrix_eq_sum_columnTuples`, the adjugate identity
`(M * adjugate M)[i][j] = if i = j then det M else 0` as `mul_adjugate_apply`,
and the three-term Plücker / Desnanot-Jacobi identity as
`det_plucker_three_term_consecutive_top`.

The identification of this determinant with Mathlib's `Matrix.det`, and the
correspondence with the executable Bareiss determinant
([`hex-bareiss`](https://github.com/kim-em/hex-bareiss)), live in the Mathlib
bridge layers.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want, and
leave the implementation to the maintainer.
