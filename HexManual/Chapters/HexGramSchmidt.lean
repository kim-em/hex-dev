/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexGramSchmidtMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexGramSchmidt: Gram-Schmidt orthogonalization" =>
%%%
tag := "hex-gram-schmidt"
%%%

# Introduction
%%%
tag := "hex-gram-schmidt-intro"
%%%

Released as
[hex-gram-schmidt](https://github.com/leanprover/hex-gram-schmidt), with the
Mathlib correspondence in
[hex-gram-schmidt-mathlib](https://github.com/leanprover/hex-gram-schmidt-mathlib).

`HexGramSchmidt` orthogonalizes the rows of a matrix by Gram-Schmidt:
from each row it subtracts the projection onto the earlier rows, and
returns the orthogonal basis together with the lower-unitriangular matrix
of projection coefficients that reconstructs the input. Everything is
phrased over {name}`Hex.Matrix`: operations take and return whole
matrices (`basis b : Matrix Rat n m`, `coeffs b : Matrix Rat n n`), and
rows are addressed by `Nat` indices with explicit bounds rather than
`Fin`.

The library has two namespaces. `Hex.GramSchmidt.Rat` orthogonalizes a
rational matrix directly. `Hex.GramSchmidt.Int` works on an integer
matrix, and its *computable* operations — the leading Gram determinants
and the integer scaled coefficient matrix — stay entirely in exact
integer arithmetic. That is the whole point of the integer namespace:
lattice code reads the exact `gramDet` and `scaledCoeffs` values and
never leaves `Int`. The orthogonal basis and rational coefficients
themselves involve division, which is usually a performance bottleneck,
so {name}`Hex.GramSchmidt.Rat.basis` and {name}`Hex.GramSchmidt.Rat.coeffs`
are `noncomputable`. The computable determinant operations
({name}`Hex.GramSchmidt.Int.gramDet`,
{name}`Hex.GramSchmidt.Int.scaledCoeffs`) drive the worked examples below.

`HexGramSchmidt` is Mathlib-free and depends only on `HexMatrix`. `HexLLL`
uses it for orthogonalization and the exact-update formulas. See
{ref "hex-gram-schmidt-cross-references"}[Cross-references].

# Fundamental operations
%%%
tag := "hex-gram-schmidt-core"
%%%

The two fundamental constructions are the orthogonal basis and the
coefficient matrix. The basis rows are mutually orthogonal. The
coefficient matrix is lower-unitriangular and reconstructs the input as
`coeffs · basis`. Both come in a rational and an integer flavour; the
integer flavour orthogonalizes over `Rat`, so like the rational one it is
`noncomputable` and exists to state theorems, not to run.

{docstring Hex.GramSchmidt.Rat.basis}

{docstring Hex.GramSchmidt.Rat.coeffs}

{docstring Hex.GramSchmidt.Int.basis}

{docstring Hex.GramSchmidt.Int.coeffs}

Both matrices are `noncomputable`, because their entries involve
division; they are stated by signature here, and their role is to be the
subject of theorems rather than something you evaluate. What you actually
compute with is the pair of exact-integer operations the integer
namespace adds. The leading Gram determinants are the determinants of the
leading principal Gram minors `B Bᵀ` (the squared volumes of the prefix
sublattices). The scaled coefficient matrix clears the denominators of
the rational coefficients against them, so every entry is again an
integer.

{docstring Hex.GramSchmidt.Int.gramDet}

{docstring Hex.GramSchmidt.Int.scaledCoeffs}

The scaled coefficients are packaged together with the Gram-determinant
vector inside {name}`Hex.GramSchmidt.Int.Data`. `scaledCoeffs` projects
out its coefficient matrix.

## Worked example: Gram determinants and scaled coefficients
%%%
tag := "hex-gram-schmidt-worked"
%%%

The block below works over the integer matrix with rows `(1,1,0)`,
`(1,0,1)`, `(0,1,1)`. It reads off the leading Gram determinants, prints
the whole scaled coefficient matrix, and applies a size-reduction row
operation. The `gramDet` bound is filled by its `by omega` autoparam, so
the calls need no explicit proof.

```lean (name := gramWorked)
open Hex Hex.GramSchmidt Hex.GramSchmidt.Int

namespace HexGramSchmidtChapter

-- A 3×3 integer matrix with rows
--   (1,1,0), (1,0,1), (0,1,1).
private def m : Hex.Matrix Int 3 3 :=
  #m[1, 1, 0; 1, 0, 1; 0, 1, 1]

-- Leading Gram determinants d_0 .. d_3. The empty
-- prefix is 1 by convention; d_k is the determinant
-- of the k×k leading Gram minor of the input.
#guard gramDet m 0 = 1
#guard gramDet m 1 = 2
#guard gramDet m 2 = 3
#guard gramDet m 3 = 4

-- scaledCoeffs stores d_{j+1} on the diagonal, the
-- integral coefficients d_{j+1}·μ_{i,j} strictly
-- below it, and zeros above.
#eval scaledCoeffs m

-- Size-reducing row 2 against row 0 by 2 replaces
-- b[2] = (0,1,1) with b[2] - 2·b[0] = (-2,-1,1).
#guard (sizeReduce m 0 2 2).row 2 = #v[-2, -1, 1]

end HexGramSchmidtChapter
```
```leanOutput gramWorked
#m[2, 0, 0;
   1, 3, 0;
   1, 1, 4]
```

# Key correctness theorems
%%%
tag := "hex-gram-schmidt-correctness"
%%%

The defining guarantee is orthogonality: distinct basis rows have zero
dot product. The statement is given over both the rational and the
integer input (the latter taken in `Rat`).

{docstring Hex.GramSchmidt.Rat.basis_orthogonal}

{docstring Hex.GramSchmidt.Int.basis_orthogonal}

The basis and coefficient matrices together factor the input. Each
input row equals its orthogonalized basis row plus the
coefficient-weighted combination of the earlier basis rows: the
triangular factorization `b = coeffs · basis`, stated row by row.

{docstring Hex.GramSchmidt.Rat.basis_decomposition}

{docstring Hex.GramSchmidt.Int.basis_decomposition}

The coefficient matrix is lower-unitriangular, and its strictly
lower entries are exactly the projection coefficients of the input row
onto the earlier basis row.

{docstring Hex.GramSchmidt.Rat.coeffs_diag}

{docstring Hex.GramSchmidt.Rat.coeffs_upper}

{docstring Hex.GramSchmidt.Rat.coeffs_lower_projection}

# Row-operation updates
%%%
tag := "hex-gram-schmidt-updates"
%%%

Lattice reduction modifies the input by elementary row operations and
needs to know how the Gram-Schmidt data changes. `HexGramSchmidt`
packages the two operations LLL uses (size reduction and adjacent swap)
and states the resulting update formulas. The row operations themselves
live in `HexMatrix`. `HexGramSchmidt` supplies the API for reasoning
about their effect on the Gram-Schmidt data.

{docstring Hex.GramSchmidt.Int.sizeReduce}

{docstring Hex.GramSchmidt.Int.adjacentSwap}

Size reduction subtracts an integer multiple of an earlier row from a
later one. This unimodular operation leaves the entire Gram-Schmidt basis
unchanged, so LLL can size-reduce freely without changing the
orthogonalized vectors or the Gram determinants the swap step depends on.

{docstring Hex.GramSchmidt.Int.basis_sizeReduce}

An adjacent swap exchanges rows `k - 1` and `k`, and the two basis rows
at those positions change. The update formulas give the new vectors as
explicit closed forms in the old data, so a caller can recompute the
updated orthogonal vectors and their norms without rerunning
Gram-Schmidt.

{docstring Hex.GramSchmidt.Int.basis_adjacentSwap_prev}

{docstring Hex.GramSchmidt.Int.basis_adjacentSwap_curr}

# The Mathlib correspondence
%%%
tag := "hex-gram-schmidt-mathlib"
%%%

Everything above is executable and Mathlib-free. `HexGramSchmidtMathlib`
connects it to Mathlib's real-valued Gram-Schmidt. The orthogonalized
basis agrees, row by row, with Mathlib's `InnerProductSpace.gramSchmidt`
after coercing the rows into a Euclidean space.

{docstring Hex.GramSchmidtMathlib.int_basis_row_eq_gramSchmidt}

The exact-integer data is tied back to that real picture too: the leading
Gram determinant is the product of the squared Gram-Schmidt norms, and
the integer scaled coefficient below the diagonal factors as
`gramDet (j+1) · μ_{i,j}` — the identity that makes the coefficients
integral.

{docstring Hex.GramSchmidt.Int.gramDet_eq_prod_normSq}

{docstring Hex.GramSchmidt.Int.scaledCoeffs_eq}

# Cross-references
%%%
tag := "hex-gram-schmidt-cross-references"
%%%

`HexGramSchmidt` depends only on `HexMatrix` and underpins `HexLLL`:

* `HexMatrix` supplies the {name}`Hex.Matrix` representation and the row
  operations (`rowAdd`, `rowSwap`) that the
  {ref "hex-gram-schmidt-updates"}[update formulas] reason about. The
  orthogonalization here is built entirely on that representation.
* `HexGramSchmidtMathlib` re-exports this executable theory as theorems
  about Mathlib's `LinearMap` and `Matrix` Gram-Schmidt. `HexGramSchmidt`
  itself imports only `HexMatrix` and `Std`.
* `HexLLL` consumes the {ref "hex-gram-schmidt-core"}[integer data]
  (the Gram determinants and scaled coefficients) and the
  {ref "hex-gram-schmidt-updates"}[exact update formulas] to drive
  lattice reduction in integer arithmetic.
