/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexMatrix

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexMatrix: dense matrices and arithmetic" =>
%%%
tag := "hex-matrix"
%%%

# Introduction
%%%
tag := "hex-matrix-intro"
%%%

`HexMatrix` is the dense matrix core of the stack: the `Matrix` type,
its constructors and readers, matrix and matrix-vector arithmetic, the
elementary row and column operations, and the submatrix and Gram-matrix
helpers. Everything here is executable and exact — entries are honest
values of the coefficient type, never floating point — so the type
doubles as both the computational engine the rest of the project calls
and the reference representation its correctness proofs are stated
against. The type is generic over the coefficient ring `R`; the
integer- and rational-valued instances are the ones the rest of the
stack uses.

The library is deliberately small and self-contained: it has no library
dependencies at all, building directly on Lean's `Vector`. The three
algorithms that sit on top of it each live in their own sibling
library: the Leibniz determinant in {ref "hex-determinant"}[HexDeterminant],
the Gauss-Jordan row reduction in {ref "hex-row-reduce"}[HexRowReduce],
and the fraction-free integer determinant in {ref "hex-bareiss"}[HexBareiss].
This chapter walks the type, its arithmetic, and the elementary
operations, and closes with a worked example that is checked when the
chapter is built.

`HexMatrix` is Mathlib-free. The `Semiring` / `Ring` structure on
square matrices, the `One` instance, and the equivalence with Mathlib's
abstract `Matrix` all live one boundary away in the forthcoming
`HexMatrixMathlib` correspondence library; this chapter states where
that boundary falls.

# The dense matrix type
%%%
tag := "hex-matrix-core"
%%%

A matrix is a vector of rows, each a vector of entries, so an `n × m`
matrix over `R` is exactly `n` rows of width `m`. The type is a thin
`abbrev` over that nested-vector representation, which keeps entry
access and the row and column readers definitionally simple.

{name}`Hex.Matrix` is the dense matrix type itself.

The principal constructor builds a matrix from an entry function; the
row, column, and transpose readers are its inverses.

{docstring Hex.Matrix.ofFn}

{docstring Hex.Matrix.row}

{docstring Hex.Matrix.col}

{docstring Hex.Matrix.transpose}

{docstring Hex.Matrix.transpose_transpose}

The all-zero matrix is the additive unit, exposed through the standard
`Zero` instance; the identity is the function {name}`Hex.Matrix.identity`.
There is deliberately no `One` instance here — that, with the rest of
the multiplicative `Semiring` / `Ring` structure, lives in
`HexMatrixMathlib`, so the Mathlib-free core stays free of the algebraic
typeclasses.

{docstring Hex.Matrix.zero}

{docstring Hex.Matrix.identity}

Multiplication is the usual row-by-column dot product, available both
matrix-by-vector and matrix-by-matrix, with `*` notation for each. The
dot product itself is exposed directly.

{docstring Vector.dotProduct}

{docstring Hex.Matrix.mulVec}

{docstring Hex.Matrix.mul}

Multiplication by the identity is the identity, and matrix
multiplication is associative — the algebraic facts the determinant and
echelon proofs lean on.

{docstring Hex.Matrix.identity_mulVec}

{docstring Hex.Matrix.mul_assoc}

A handful of derived vector and matrix readers round out the core: the
squared Euclidean norm and its integer and rational specializations, the
Gram matrix of the rows, and the leading principal submatrices used by
the Bareiss recurrence.

{docstring Hex.Matrix.gramMatrix}

{docstring Hex.Matrix.principalSubmatrix}

# Elementary operations
%%%
tag := "hex-matrix-elementary"
%%%

The elementary row operations are the building blocks of the echelon
transforms, and each carries a determinant law (stated and proved in
{ref "hex-determinant"}[HexDeterminant]). They operate on a matrix over
any ring; the {ref "hex-row-reduce"}[HexRowReduce] reductions that use
them specialize to a field, where division by a pivot is available.

{docstring Hex.Matrix.rowSwap}

{docstring Hex.Matrix.rowScale}

{docstring Hex.Matrix.rowAdd}

# Worked example
%%%
tag := "hex-matrix-worked"
%%%

The block below builds the integer matrix with rows `(2, 0, 1)`,
`(1, 3, 2)`, and `(0, 1, 1)`, and reads a few core quantities off it:
the squared norm of the first row is `2² + 0² + 1² = 5`, the dot product
of the first two rows is `2·1 + 0·3 + 1·2 = 4`, and multiplying a vector
by the identity returns it unchanged. Every `#guard` is checked when the
chapter is built, so the outputs are guaranteed to match the executable
implementation.

```lean
open Hex Hex.Matrix

namespace HexMatrixChapterExample

-- A = [[2, 0, 1], [1, 3, 2], [0, 1, 1]].
private def A : Matrix Int 3 3 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 2 | 0, 1 => 0 | 0, 2 => 1
    | 1, 0 => 1 | 1, 1 => 3 | 1, 2 => 2
    | 2, 0 => 0 | 2, 1 => 1 | 2, 2 => 1
    | _, _ => 0

-- The squared norm of the first row is 5.
#guard Vector.normSq (Matrix.row A 0) = 5

-- The dot product of the first two rows is 4.
#guard (Matrix.row A 0).dotProduct (Matrix.row A 1) = 4

-- The identity fixes every vector under mulVec.
private def v : Vector Int 3 :=
  Vector.ofFn fun i => (i.val + 1 : Int)

#guard Matrix.mulVec (Matrix.identity (R := Int) 3) v = v

end HexMatrixChapterExample
```

# Cross-references
%%%
tag := "hex-matrix-cross-references"
%%%

`HexMatrix` sits at the base of the linear-algebra stack:

* It has no library dependencies — the matrix type, its arithmetic, and
  the elementary operations are all built directly on Lean's `Vector`,
  with no other `hex-*` library underneath.
* {ref "hex-determinant"}[HexDeterminant], {ref "hex-row-reduce"}[HexRowReduce],
  and {ref "hex-bareiss"}[HexBareiss] each build on this core: the
  Leibniz determinant and its cofactor theory, the Gauss-Jordan row
  reduction with its span and nullspace readers, and the fraction-free
  integer determinant, respectively.
* `HexMatrixMathlib` is the correspondence library carrying the
  `Semiring` / `Ring` structure, the `One` instance, and the soundness
  theorems that relate this executable representation to Mathlib's
  abstract `Matrix` API. The Mathlib dependency lives entirely on that
  side of the boundary; `HexMatrix` itself is Mathlib-free.
