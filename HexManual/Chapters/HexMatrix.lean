/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexMatrix.Basic
import HexDeterminant
import HexRowReduce.RowEchelon
import HexRowReduce.RREF
import HexBareiss.Bareiss

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexMatrix: dense linear algebra over Int" =>
%%%
tag := "hex-matrix"
%%%

# Introduction
%%%
tag := "hex-matrix-intro"
%%%

`HexMatrix` is the dense matrix core of the stack: the `Matrix` type and
its arithmetic, a Leibniz determinant, the fraction-free Bareiss
determinant algorithm over the integers, and the row-echelon and
reduced-row-echelon transforms with their span and nullspace readers.
Everything here is executable and exact — entries are honest `Int` (or,
for the field-valued reductions, `Rat`) values, never floating point —
so the algorithms double as both the computational engine the rest of
the project calls and the reference semantics its correctness proofs are
stated against.

The library is deliberately small and self-contained: it has no library
dependencies at all. Downstream, the integer Gram-Schmidt layer reads
its matrices off this type, the lattice-reduction path manipulates
bases as `Matrix Int` rows, and the factorization stack uses the Bareiss
determinant where a fraction-free exact integer determinant is wanted.
This chapter walks the type and its operations, then the two
determinant routes (Leibniz and Bareiss), then the echelon transforms,
and closes with a worked determinant example that is checked when the
chapter is built.

`HexMatrix` is Mathlib-free. The theorems identifying its executable
routines with the abstract Mathlib `Matrix` determinant live one
boundary away in the forthcoming `HexMatrixMathlib` correspondence
library; this chapter states where that boundary falls.

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

The all-zero and identity matrices are the additive and multiplicative
units, exposed through the standard `Zero` and `One` instances.

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

{docstring Hex.Matrix.one_mulVec}

{docstring Hex.Matrix.mul_assoc}

A handful of derived vector and matrix readers round out the core: the
squared Euclidean norm and its integer and rational specializations, the
Gram matrix of the rows, and the leading principal submatrices used by
the Bareiss recurrence.

{docstring Hex.Matrix.gramMatrix}

{docstring Hex.Matrix.principalSubmatrix}

# The determinant
%%%
tag := "hex-matrix-determinant"
%%%

The reference determinant is the Leibniz formula: a signed sum over all
permutation vectors of the product of the selected entries. It is the
definitional semantics — correct by construction, but factorially slow,
so it serves as the specification the faster Bareiss route is checked
against rather than the routine a caller invokes on a large matrix.

{docstring Hex.Matrix.det}

The classical row and column laws are all proved against this
definition. Swapping two rows negates the determinant; scaling a row
scales it; adding a multiple of one row to another leaves it unchanged;
and the determinant is invariant under transpose.

{docstring Hex.Matrix.det_one}

{docstring Hex.Matrix.det_rowSwap}

{docstring Hex.Matrix.det_rowScale}

{docstring Hex.Matrix.det_rowAdd}

{docstring Hex.Matrix.det_transpose}

{docstring Hex.Matrix.det_colSwap}

# The Bareiss determinant
%%%
tag := "hex-matrix-bareiss"
%%%

For an actual integer determinant computation the library uses Bareiss
elimination: a fraction-free Gaussian elimination in which every
intermediate entry stays an exact integer because each update divides
*exactly* by the previous pivot. It runs in cubic time and never leaves
the integers, so it avoids both the factorial blow-up of the Leibniz
sum and the denominators of ordinary Gaussian elimination.

An elimination pass returns a small record: the terminal matrix, the
number of row swaps performed during pivoting, and an optional record of
the first step at which a zero pivot with no replacement row was found
(the signal that the matrix is singular).

{docstring Hex.Matrix.BareissData}

The sign contributed by the row swaps and the encoded determinant are
read off that record. A recorded singular step encodes determinant zero;
otherwise the determinant is the last diagonal entry of the terminal
matrix with the swap sign applied.

{docstring Hex.Matrix.BareissData.sign}

{docstring Hex.Matrix.BareissData.det}

The public entry points run the row-pivoting elimination. {name}`Hex.Matrix.bareissData`
returns the full record; {name}`Hex.Matrix.bareiss` returns just the
integer determinant.

{docstring Hex.Matrix.bareissData}

{docstring Hex.Matrix.bareiss}

This is where the computational/proof boundary falls. The Mathlib-free
layer proves the internal structural facts about the elimination — for
instance that the packaged record is exactly the structured pivot loop
finished into determinant data — but it does *not* prove that the
Bareiss determinant equals the Leibniz {name}`Hex.Matrix.det`. That
identification is a correspondence theorem living in the forthcoming
`HexMatrixMathlib` bridge. Within `HexMatrix` itself the agreement is
pinned only as value-level conformance fixtures: a fixed bank of
matrices on which `Hex.Matrix.bareiss M = Hex.Matrix.det M` is checked
at build time.

{docstring Hex.Matrix.bareissData_eq_finish_pivotLoop}

# Row echelon and reduced row echelon
%%%
tag := "hex-matrix-echelon"
%%%

The elementary row operations are the building blocks of the echelon
transforms, and each carries the determinant law quoted above. They
operate on a matrix over any ring; the reductions that follow specialize
to a field, where division by a pivot is available.

{docstring Hex.Matrix.rowSwap}

{docstring Hex.Matrix.rowScale}

{docstring Hex.Matrix.rowAdd}

An echelon computation returns its result packaged with a certificate of
how it got there: the rank, the reduced matrix, the accumulated
invertible row-operation transform `T` with `T * original = echelon`,
and the pivot column of each row.

{docstring Hex.Matrix.RowEchelonData}

Two predicates capture what it means for such a record to be a genuine
echelon or reduced-echelon form. {name}`Hex.Matrix.IsEchelonForm` bundles
the conditions shared by any echelon form — the transform equation, the
transform's invertibility, the rank bounds, and the staircase pivot
structure. {name}`Hex.Matrix.IsRREF` extends it with the two
reduced-form conditions: each pivot is one, and every entry above a
pivot is zero.

{name}`Hex.Matrix.IsEchelonForm` and {name}`Hex.Matrix.IsRREF` are those
two predicates.

The driver is Gauss-Jordan elimination, returning a
{name}`Hex.Matrix.RowEchelonData` whose record satisfies the
reduced-form contract.

{docstring Hex.Matrix.rref}

{docstring Hex.Matrix.rref_transform_mul}

{docstring Hex.Matrix.rref_isRREF}

On top of the reduced form sit the linear-algebra readers a caller
actually wants: membership in the row span with an explicit witness, the
boolean span test, and a basis for the nullspace — each with a soundness
theorem tying the executable answer back to the matrix.

{docstring Hex.Matrix.spanCoeffs}

{docstring Hex.Matrix.spanContains}

{docstring Hex.Matrix.nullspace}

# Worked example
%%%
tag := "hex-matrix-worked"
%%%

The block below builds the integer matrix with rows `(2, 0, 1)`,
`(1, 3, 2)`, and `(0, 1, 1)`, whose determinant is `3`. Both determinant
routes agree on it, and both agree with each other; the identity has
determinant one, the determinant is invariant under transpose, and a
matrix with a repeated-up-to-scale row is singular. Every `#guard` is
checked when the chapter is built, so the outputs are guaranteed to
match the executable implementation.

```lean
open Hex Hex.Matrix

namespace HexMatrixChapterExample

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

-- The Bareiss determinant agrees with Leibniz.
#guard Matrix.bareiss A = Matrix.det A

-- The determinant is invariant under transpose.
#guard Matrix.det (Matrix.transpose A) = 3

-- The identity has determinant one, both routes.
#guard Matrix.det (1 : Matrix Int 3 3) = 1
#guard Matrix.bareiss (1 : Matrix Int 3 3) = 1

-- S = [[1, 2], [2, 4]] has a dependent row pair,
-- so its determinant is zero.
private def S : Matrix Int 2 2 :=
  Matrix.ofFn fun i j =>
    match i.val, j.val with
    | 0, 0 => 1 | 0, 1 => 2
    | 1, 0 => 2 | 1, 1 => 4
    | _, _ => 0

#guard Matrix.det S = 0
#guard Matrix.bareiss S = 0

end HexMatrixChapterExample
```

# Cross-references
%%%
tag := "hex-matrix-cross-references"
%%%

`HexMatrix` sits at the base of the linear-algebra stack:

* It has no library dependencies — the matrix type, its arithmetic, both
  determinant routes, and the echelon transforms are all built directly
  on Lean's `Vector`, with no other `hex-*` library underneath.
* `HexMatrixMathlib` is the correspondence library carrying the
  soundness theorems that relate these executable routines to Mathlib's
  abstract `Matrix` API — in particular the identification of the
  {name}`Hex.Matrix.bareiss` determinant with the Leibniz
  {name}`Hex.Matrix.det` and with Mathlib's determinant. That chapter is
  forthcoming; until it lands, the agreement between the two determinant
  routes is exercised here only through the conformance fixtures
  described in the {ref "hex-matrix-bareiss"}[Bareiss section]. The
  Mathlib dependency lives entirely on that side of the boundary;
  `HexMatrix` itself is Mathlib-free.
