/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexMatrixMathlib

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

`Hex.Matrix R n m` is an `n × m` matrix over `R`.

This library has the type, its arithmetic (the dot product, matrix-vector
and matrix-matrix multiplication, transpose, the Gram matrix), and the
elementary row and column operations. It depends on no other `hex`
library. The determinant, row reduction, and integer determinant are
separate libraries built on it: {ref "hex-determinant"}[HexDeterminant],
{ref "hex-row-reduce"}[HexRowReduce], {ref "hex-bareiss"}[HexBareiss].

The type and its operations are Mathlib-free. The
{ref "hex-matrix-mathlib"}[last section] connects them to Mathlib: the
`Semiring`/`Ring` and `One` instances, and the identification with
Mathlib's `Matrix`.

# The dense matrix type
%%%
tag := "hex-matrix-core"
%%%

{name}`Hex.Matrix.ofFn` builds a matrix from an entry function
`Fin n → Fin m → R`; `row`, `col`, and `transpose` read it back.

{docstring Hex.Matrix.ofFn}

{docstring Hex.Matrix.row}

{docstring Hex.Matrix.col}

{docstring Hex.Matrix.transpose}

{docstring Hex.Matrix.transpose_transpose}

The zero and identity matrices:

{docstring Hex.Matrix.zero}

{docstring Hex.Matrix.identity}

Multiplication is the row-by-column dot product, matrix-vector and
matrix-matrix, both written `*`.

{docstring Vector.dotProduct}

{docstring Hex.Matrix.mulVec}

{docstring Hex.Matrix.mul}

The identity is a left and right unit, and multiplication is associative.

{docstring Hex.Matrix.identity_mulVec}

{docstring Hex.Matrix.mul_assoc}

The squared norm of a vector, the Gram matrix of the rows, and the
leading principal submatrices the Bareiss recurrence uses:

{docstring Hex.Matrix.gramMatrix}

{docstring Hex.Matrix.principalSubmatrix}

# Elementary operations
%%%
tag := "hex-matrix-elementary"
%%%

The elementary row operations work over any ring. Each has a determinant
law, proved in {ref "hex-determinant"}[HexDeterminant];
{ref "hex-row-reduce"}[HexRowReduce] uses them for Gauss-Jordan reduction
over a field.

{docstring Hex.Matrix.rowSwap}

{docstring Hex.Matrix.rowScale}

{docstring Hex.Matrix.rowAdd}

# Worked example
%%%
tag := "hex-matrix-worked"
%%%

The block builds an integer matrix with the `#m[...]` literal and reads
three quantities off it: the squared norm of the first row
(`2² + 0² + 1² = 5`), the dot product of the first two rows (`4`), and
that the identity fixes a vector. Each `#guard` is checked when the
chapter builds.

```lean
open Hex

namespace HexMatrixChapterExample

def A : Matrix Int 3 3 := #m[2, 0, 1; 1, 3, 2; 0, 1, 1]

#guard (A.row 0).normSq = 5

#guard (A.row 0).dotProduct (A.row 1) = 4

def v : Vector Int 3 := #v[1, 2, 3]

#guard (Matrix.identity (R := Int) 3).mulVec v = v

end HexMatrixChapterExample
```

# The Mathlib correspondence
%%%
tag := "hex-matrix-mathlib"
%%%

Everything above is executable and Mathlib-free. `HexMatrixMathlib`
connects it to Mathlib: every `Hex.Matrix` corresponds to a Mathlib
`Matrix` with the same entries.

{docstring HexMatrixMathlib.matrixEquiv}

The `Semiring`, `Ring`, and `Algebra` structure on square matrices, and
the `One` instance, are defined by transport through
{name}`HexMatrixMathlib.matrixEquiv`, bundled
as {name}`HexMatrixMathlib.matrixRingEquiv` and
{name}`HexMatrixMathlib.matrixAlgEquiv`. The elementary row operations
become Mathlib's elementary matrices
({name}`HexMatrixMathlib.matrixEquiv_rowSwap`,
{name}`HexMatrixMathlib.matrixEquiv_rowScale`,
{name}`HexMatrixMathlib.matrixEquiv_rowAdd`).

# Cross-references
%%%
tag := "hex-matrix-cross-references"
%%%

Downstream of `HexMatrix`:

* {ref "hex-determinant"}[HexDeterminant]: the Leibniz determinant,
  cofactors, and the adjugate.
* {ref "hex-row-reduce"}[HexRowReduce]: Gauss-Jordan reduction, the row
  span, and the nullspace.
* {ref "hex-bareiss"}[HexBareiss]: the fraction-free integer determinant.
