/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexDeterminant

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
coefficient ring; the row-operation, Laplace, Cauchy-Binet, and Plücker
results hold over a commutative ring.

The Leibniz determinant is the definition: correct by construction but
factorially slow, so it is the specification the faster
{ref "hex-bareiss"}[HexBareiss] route is checked against, not the routine
a caller runs on a large matrix.

`HexDeterminant` is Mathlib-free. The identification of this determinant
with Mathlib's `Matrix.det`, and with the executable Bareiss
determinant, lives in `HexDeterminantMathlib` and
`HexBareissMathlib`.

# The Leibniz determinant
%%%
tag := "hex-determinant-leibniz"
%%%

The reference determinant is the Leibniz formula: a signed sum over all
permutation vectors of the product of the selected entries.

{docstring Hex.Matrix.det}

The classical row and column laws are all proved against this
definition. The identity has determinant one; swapping two rows negates
the determinant; scaling a row scales it; adding a multiple of one row
to another leaves it unchanged; and the determinant is invariant under
transpose.

{docstring Hex.Matrix.det_identity}

{docstring Hex.Matrix.det_rowSwap}

{docstring Hex.Matrix.det_rowScale}

{docstring Hex.Matrix.det_rowAdd}

{docstring Hex.Matrix.det_transpose}

{docstring Hex.Matrix.det_colSwap}

The determinant is linear in each column separately; the additive law in
one column is the building block for Laplace expansion.

{docstring Hex.Matrix.det_setCol_add}

# Cofactor expansion
%%%
tag := "hex-determinant-cofactor"
%%%

Deleting one row and one column gives a minor; the signed minor is a
cofactor, and the determinant is the alternating sum of entries against
their cofactors along any fixed row or column.

{docstring Hex.Matrix.deleteRowCol}

{docstring Hex.Matrix.cofactorSign}

{docstring Hex.Matrix.cofactor}

{docstring Hex.Matrix.det_eq_foldl_laplace_row}

# The adjugate
%%%
tag := "hex-determinant-adjugate"
%%%

The adjugate is the transpose of the cofactor matrix. Its defining
identity, `M * adjugate M = det M • identity`, is the executable
Cramer's-rule kernel: over a commutative ring it holds without any
invertibility hypothesis.

{docstring Hex.Matrix.adjugate}

{docstring Hex.Matrix.mul_adjugate}

# Cauchy-Binet and Plücker identities
%%%
tag := "hex-determinant-identities"
%%%

The determinant of a Gram matrix expands as a sum over column tuples
(the Cauchy-Binet formula), and the three-term Plücker /
Desnanot-Jacobi identity relates the determinants of a matrix and its
bordered minors. The triangular-determinant law reads the determinant
of an upper- or lower-triangular matrix off its diagonal.

{docstring Hex.Matrix.det_gramMatrix_eq_sum_columnTuples}

{docstring Hex.Matrix.det_plucker_three_term_consecutive_top}

{docstring Hex.Matrix.det_upperTriangular_eq_foldl_diag}

# Worked example
%%%
tag := "hex-determinant-worked"
%%%

The block below builds the integer matrix with rows `(2, 0, 1)`,
`(1, 3, 2)`, and `(0, 1, 1)`, whose determinant is `3`. The identity has
determinant one, the determinant is invariant under transpose, swapping
two rows negates it, and a matrix with a dependent row pair is singular.
Every `#guard` is checked when the chapter is built.

```lean
open Hex Hex.Matrix

namespace HexDeterminantChapterExample

-- A = [[2, 0, 1], [1, 3, 2], [0, 1, 1]], det = 3.
private def A : Matrix Int 3 3 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 2 | 0, 1 => 0 | 0, 2 => 1
    | 1, 0 => 1 | 1, 1 => 3 | 1, 2 => 2
    | 2, 0 => 0 | 2, 1 => 1 | 2, 2 => 1
    | _, _ => 0

-- The Leibniz determinant evaluates to 3.
#guard Matrix.det A = 3

-- The determinant is invariant under transpose.
#guard Matrix.det (Matrix.transpose A) = 3

-- Swapping two rows negates the determinant.
#guard Matrix.det (Matrix.rowSwap A 0 1) = -3

-- The identity has determinant one.
#guard Matrix.det (Matrix.identity (R := Int) 3) = 1

-- S = [[1, 2], [2, 4]] has a dependent row pair,
-- so its determinant is zero.
private def S : Matrix Int 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1 | 0, 1 => 2
    | 1, 0 => 2 | 1, 1 => 4
    | _, _ => 0

#guard Matrix.det S = 0

end HexDeterminantChapterExample
```

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
