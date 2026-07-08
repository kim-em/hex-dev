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

Released as [hex-matrix](https://github.com/leanprover/hex-matrix), with the
Mathlib correspondence in
[hex-matrix-mathlib](https://github.com/leanprover/hex-matrix-mathlib).

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

This section is the definitions; the {ref "hex-matrix-lemmas"}[next
section] collects the theorems about them.

{name}`Hex.Matrix.ofFn` builds a matrix from an entry function
`Fin n → Fin m → R`. `row` and `col` return its rows and columns, and
`transpose` swaps them.

{docstring Hex.Matrix.ofFn}

{docstring Hex.Matrix.row}

{docstring Hex.Matrix.col}

{docstring Hex.Matrix.transpose}

The zero and identity matrices:

{docstring Hex.Matrix.zero}

{docstring Hex.Matrix.identity}

Matrix-vector and matrix-matrix multiplication are both written `*`.
Each product entry is a row-by-column dot product.

{docstring Vector.dotProduct}

{docstring Hex.Matrix.mulVec}

{docstring Hex.Matrix.mul}

The Gram matrix of the rows and the leading principal submatrices used by
the Bareiss recurrence:

{docstring Hex.Matrix.gramMatrix}

{docstring Hex.Matrix.principalSubmatrix}

# Arithmetic worked example
%%%
tag := "hex-matrix-arithmetic"
%%%

A compact tour of the core arithmetic: {name}`Hex.Matrix.getRow` reads a
row and `M[(i, j)]` reads a single entry, {name}`Hex.Matrix.mulVec`
multiplies by a vector, and `+`, `•`, and {name}`Hex.Matrix.identity` are
the entrywise sum, scalar action, and identity.

```lean
open Hex

namespace HexMatrixArithmetic

def M : Matrix Int 2 2 := #m[1, 2; 3, 4]
def v : Vector Int 2 := #v[5, 6]

-- A single entry, read with M[(row, col)].
def corner : Int := M[(1, 1)]

-- getRow reads a whole row; `corner` holds one entry.
#guard M.getRow 1 = #v[3, 4]
#guard corner = 4

-- Matrix-vector product, entrywise sum, scalar action.
#guard M.mulVec v = #v[17, 39]
#guard M + M = #m[2, 4; 6, 8]
#guard (2 : Int) • M = #m[2, 4; 6, 8]

-- The identity fixes every vector.
#guard (Matrix.identity (R := Int) 2).mulVec v = v

end HexMatrixArithmetic
```

# Entry, row, and column lemmas
%%%
tag := "hex-matrix-lemmas"
%%%

Every operation above carries a complete set of description lemmas: an
entry lemma `getElem_…` fixing `M[i][j]`, and `row_…`/`col_…` lemmas
fixing a whole row or column. This grid is kept total — `zero`,
`identity`, `transpose`, `mulVec`, `vecMul`, `mul`, `gramMatrix`,
`principalSubmatrix`, and every elementary operation each carry all
three — so a proof can rewrite in whichever shape it needs. The lemmas
below are representative rather than exhaustive.

Transpose exchanges rows and columns, and is an involution:

{docstring Hex.Matrix.getElem_transpose}

{docstring Hex.Matrix.row_transpose}

{docstring Hex.Matrix.transpose_transpose}

Every product entry is a dot product: matrix-vector, vector-matrix, and
matrix-matrix multiplication all read off {name}`Vector.dotProduct`.

{docstring Hex.Matrix.getElem_mulVec}

{docstring Hex.Matrix.getElem_vecMul}

{docstring Hex.Matrix.getElem_mul}

The identity entries are the Kronecker delta, the identity is a left and
right unit, and multiplication is associative:

{docstring Hex.Matrix.getElem_identity}

{docstring Hex.Matrix.identity_mul}

{docstring Hex.Matrix.mul_identity}

{docstring Hex.Matrix.mul_assoc}

The Gram matrix pairs the rows against one another:

{docstring Hex.Matrix.getElem_gramMatrix}

# Elementary operations
%%%
tag := "hex-matrix-elementary"
%%%

The elementary operations work over any ring. Each row operation has a
column mirror — `rowSwap`/`colSwap`, `rowScale`/`colScale`,
`rowAdd`/`colAdd` — and each has a determinant law proved in
{ref "hex-determinant"}[HexDeterminant].
{ref "hex-row-reduce"}[HexRowReduce] uses the row operations for
Gauss-Jordan reduction over a field.

{docstring Hex.Matrix.rowSwap}

{docstring Hex.Matrix.rowScale}

{docstring Hex.Matrix.rowAdd}

{docstring Hex.Matrix.colSwap}

{docstring Hex.Matrix.colScale}

# Worked example
%%%
tag := "hex-matrix-worked"
%%%

The block builds an integer matrix with the `#m[...]` literal and checks
the squared norm of the first row (`2² + 0² + 1² = 5`), the dot product
of the first two rows (`4`), that the identity fixes a vector, and one
elementary row operation: adding row `0` to row `2` (`rowAdd A 0 2 1`)
replaces row `2 = (0, 1, 1)` with `(0, 1, 1) + (2, 0, 1) = (2, 1, 2)`.

```lean
open Hex

namespace HexMatrixChapterExample

def A : Matrix Int 3 3 := #m[2, 0, 1; 1, 3, 2; 0, 1, 1]

#guard (A.row 0).normSq = 5

#guard (A.row 0).dotProduct (A.row 1) = 4

def v : Vector Int 3 := #v[1, 2, 3]

#guard (Matrix.identity (R := Int) 3).mulVec v = v

#guard (Matrix.rowAdd A 0 2 1).row 2 = #v[2, 1, 2]

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
