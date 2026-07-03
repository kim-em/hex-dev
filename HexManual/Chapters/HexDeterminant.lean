/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexDeterminantMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexDeterminant: the Leibniz determinant and cofactor theory" =>
%%%
tag := "hex-determinant"
%%%

# Introduction
%%%
tag := "hex-determinant-intro"
%%%

Released as [hex-determinant](https://github.com/leanprover/hex-determinant),
with the Mathlib correspondence in
[hex-determinant-mathlib](https://github.com/leanprover/hex-determinant-mathlib).

`HexDeterminant` is the determinant of a dense square matrix via the
Leibniz formula, with the cofactor and adjugate theory built on it. It
depends only on {ref "hex-matrix"}[HexMatrix] and is generic over the
coefficient ring. The row-operation, Laplace, Cauchy-Binet, and Plücker
results hold over a commutative ring.

The Leibniz determinant is the definition: correct by construction but
factorially slow, so it is the specification the faster
{ref "hex-bareiss"}[HexBareiss] route is checked against, not the routine
a caller runs on a large matrix.

`HexDeterminant` is Mathlib-free. Its identification with Mathlib's
`Matrix.det` is the {ref "hex-determinant-mathlib"}[last section]; the
identification with the executable Bareiss determinant lives in
`HexBareissMathlib` and is covered in the
{ref "hex-bareiss"}[HexBareiss chapter].

# The Leibniz determinant
%%%
tag := "hex-determinant-leibniz"
%%%

The reference determinant is the Leibniz formula: a signed sum over all
permutations of the product of the selected entries.

{docstring Hex.Matrix.det}

The classical row laws are all proved against this definition. The
identity has determinant one; swapping two rows negates the determinant;
scaling a row scales it; adding a multiple of one row to another leaves
it unchanged; and the determinant is invariant under transpose.

{docstring Hex.Matrix.det_identity}

{docstring Hex.Matrix.det_rowSwap}

{docstring Hex.Matrix.det_rowScale}

{docstring Hex.Matrix.det_rowAdd}

{docstring Hex.Matrix.det_transpose}

Because the determinant is transpose-invariant, every row law has a
column mirror, proved by transposing rather than by re-deriving anything:
`det_colSwap`, `det_colScale`, and `det_colAdd` correspond to the three
row operations, and `det_setRow_add` is the row mirror of the column
linearity below.

{docstring Hex.Matrix.det_colSwap}

The determinant is linear in each column separately. The additive law in
one column is the building block for Laplace expansion.

{docstring Hex.Matrix.det_setCol_add}

# Cofactor expansion
%%%
tag := "hex-determinant-cofactor"
%%%

Deleting one row and one column gives a minor. The signed minor is a
cofactor, and the determinant is the alternating sum of entries against
their cofactors along any fixed row or column.

{docstring Hex.Matrix.deleteRowCol}

{docstring Hex.Matrix.cofactorSign}

{docstring Hex.Matrix.cofactor}

{docstring Hex.Matrix.det_eq_finFoldl_laplace_row}

# The adjugate
%%%
tag := "hex-determinant-adjugate"
%%%

The adjugate is the transpose of the cofactor matrix. Its defining
identity, `M * adjugate M = det M • identity`, is what Cramer's rule
rests on. Over a commutative ring it holds without any invertibility
hypothesis.

{docstring Hex.Matrix.adjugate}

{docstring Hex.Matrix.mul_adjugate}

# Cauchy-Binet and Plücker identities
%%%
tag := "hex-determinant-identities"
%%%

The determinant of a Gram matrix expands as a sum over column tuples
(the Cauchy-Binet formula), and the three-term Plücker /
Desnanot-Jacobi identity relates the determinants of a matrix and its
bordered minors. The triangular-determinant law gives the determinant of an upper- or
lower-triangular matrix as the product of its diagonal entries.

{docstring Hex.Matrix.det_gramMatrix_eq_sum_columnTuples}

{docstring Hex.Matrix.det_plucker_three_term_consecutive_top}

{docstring Hex.Matrix.det_upperTriangular_eq_finFoldl_diag}

# Worked example
%%%
tag := "hex-determinant-worked"
%%%

The block below builds the integer matrix with rows `(2, 0, 1)`,
`(1, 3, 2)`, and `(0, 1, 1)`, whose determinant is `3`. The identity has
determinant one, the determinant is invariant under transpose, swapping
two rows negates it, and a matrix with a dependent row pair is singular.

```lean
open Hex Hex.Matrix

namespace HexDeterminantChapterExample

-- A = [[2, 0, 1], [1, 3, 2], [0, 1, 1]], det = 3.
private def A : Hex.Matrix Int 3 3 := #m[2, 0, 1; 1, 3, 2; 0, 1, 1]

-- The Leibniz determinant evaluates to 3.
#guard det A = 3

-- The determinant is invariant under transpose.
#guard det (transpose A) = 3

-- Swapping two rows negates the determinant.
#guard det (rowSwap A 0 1) = -3

-- The identity has determinant one.
#guard det (Hex.Matrix.identity (R := Int) 3) = 1

-- S = [[1, 2], [2, 4]] has a dependent row pair,
-- so its determinant is zero.
private def S : Hex.Matrix Int 2 2 := #m[1, 2; 2, 4]

#guard det S = 0

end HexDeterminantChapterExample
```

# The Mathlib correspondence
%%%
tag := "hex-determinant-mathlib"
%%%

Everything above is executable and Mathlib-free. `HexDeterminantMathlib`
connects it to Mathlib: the Leibniz determinant `Hex.Matrix.det` equals
Mathlib's `Matrix.det` of the corresponding Mathlib matrix, transported
through {name}`HexMatrixMathlib.matrixEquiv` (the same equivalence the
{ref "hex-matrix-mathlib"}[HexMatrix chapter] introduces).

{docstring HexMatrixMathlib.det_eq}

So a fact about Mathlib's `Matrix.det` can be discharged by running the
executable determinant, and a fact about the executable determinant can
be proved with Mathlib's determinant theory.

# Cross-references
%%%
tag := "hex-determinant-cross-references"
%%%

`HexDeterminant` depends only on {ref "hex-matrix"}[HexMatrix], using its
matrix type, arithmetic, and elementary operations (whose determinant
laws are proved here).

* {ref "hex-bareiss"}[HexBareiss] computes the same integer determinant
  fraction-free in cubic time, using this Leibniz `det` as its
  specification.
* `HexDeterminantMathlib` identifies this executable determinant with
  Mathlib's `Matrix.det`. `HexDeterminant` itself is Mathlib-free.
