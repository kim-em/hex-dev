# hex-determinant

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

`hex-determinant` provides the determinant of a dense square matrix via the
Leibniz formula, together with the cofactor and adjugate theory. This library
depends only on [`hex-matrix`](https://github.com/leanprover/hex-matrix). See
[`hex-determinant-mathlib`](https://github.com/leanprover/hex-determinant-mathlib)
for the correspondence with Mathlib's types and theory.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-determinant"
git = "https://github.com/leanprover/hex-determinant.git"
rev = "main"
```

```lean
import HexDeterminant

open Hex

def M : Matrix Int 3 3 := Matrix.ofFn fun i j => if i = j then (2 : Int) else 1

#eval Matrix.det M                       -- 4, via the Leibniz formula
#eval Matrix.det (Matrix.identity (R := Int) 4)    -- 1

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
`det_identity` and the row-operation laws `det_rowSwap`, `det_rowScale`, and
`det_rowAdd`.

The headline theorem for each of the remaining results (with
`[Lean.Grind.CommRing R]` throughout):

Column linearity, `det_setCol_add`:

```lean
theorem det_setCol_add (M : Matrix R n n) (dst : Fin n) (v w : Fin n → R) :
    det (setCol M dst (fun r => v r + w r)) =
      det (setCol M dst v) + det (setCol M dst w)
```

Laplace cofactor expansion along a row, `det_eq_finFoldl_laplace_row`:

```lean
theorem det_eq_finFoldl_laplace_row (M : Matrix R (n + 1) (n + 1)) (row : Fin (n + 1)) :
    det M =
      Fin.foldl (n + 1)
        (fun acc col => acc + M[row][col] * cofactor M row col) 0
```

The `List.finRange` reference form `det_eq_foldl_laplace_row` states the same
expansion as a `List.foldl`, bridged by `Fin.foldl_eq_finRange_foldl`.

We prove the Cauchy-Binet column-tuple product formula (Gram form) as
`det_gramMatrix_eq_sum_columnTuples` and the adjugate identity
`M * adjugate M = det M • identity` as `mul_adjugate`.

Two quadratic identities among minors are proved here, and it is worth keeping
their names apart. `det_setRow_setRow_mul_det` is the two-row replacement
identity, the `2 × 2` case of Jacobi's adjugate-minor identity: for distinct
rows `a`, `b` and arbitrary vectors `u`, `v`,

```lean
theorem det_setRow_setRow_mul_det
    (M : Matrix R (n + 1) (n + 1)) (a b : Fin (n + 1)) (hab : a ≠ b)
    (u v : Vector R (n + 1)) :
    det M * det (setRow (setRow M a u) b v) =
      det (setRow M a u) * det (setRow M b v) -
        det (setRow M a v) * det (setRow M b u)
```

`det_plucker_three_term_consecutive_top` is a three-term Grassmann-Plücker
relation, in the specialisation where the two larger of the three distinguished
rows are the last two rows. It relates the maximal minors of a tall
`B : Matrix R (k + 2) k` to those of `B` with a column appended: `nDet B p q`
deletes two rows of `B`, while `mDet B v p` deletes one row of `[B | v]`. Taking
`v` a standard basis vector recovers the ordinary six-maximal-minor relation
among `nDet`s.

Desnanot-Jacobi itself, and the unrestricted three-term relation for any
`p1 < p2 < p3`, are stated in
[`hex-determinant-mathlib`](https://github.com/leanprover/hex-determinant-mathlib).
Sylvester's determinant identity, the general `m × m` bordered-minor statement,
is not proved anywhere in the project.

The identification of this determinant with Mathlib's `Matrix.det`, and the
correspondence with the executable Bareiss determinant
([`hex-bareiss`](https://github.com/leanprover/hex-bareiss)), live in the Mathlib
bridge layers.

# Reference manual

The hex reference manual covers this library at
<https://kim-em.github.io/hex-dev/find/?domain=Verso.Genre.Manual.section&name=hex-determinant>.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in this published mirror. Contributions are welcome as pull
requests to the `SPEC/` directory: describe the behaviour you want, and
leave the implementation to the maintainer.
