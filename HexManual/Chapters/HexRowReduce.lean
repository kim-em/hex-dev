/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexRowReduceMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexRowReduce: Gauss-Jordan reduction, span, and nullspace" =>
%%%
tag := "hex-row-reduce"
%%%

# Introduction
%%%
tag := "hex-row-reduce-intro"
%%%

Released as [hex-row-reduce](https://github.com/leanprover/hex-row-reduce),
with the Mathlib correspondence in
[hex-row-reduce-mathlib](https://github.com/leanprover/hex-row-reduce-mathlib).

`HexRowReduce` does Gauss-Jordan reduction of a matrix over a field to
reduced row echelon form, and computes the row span and nullspace from
it. It depends only on {ref "hex-matrix"}[HexMatrix].

The reduction returns a certificate, not just a reduced matrix: the rank,
the reduced form, an invertible transform `T` with `T * original =
echelon`, and the pivot columns. The span and nullspace operations are
computed from it, each proved correct for the original matrix `M` by a
soundness theorem (the nullspace basis also has a completeness theorem).

`HexRowReduce` is Mathlib-free. `HexRowReduceMathlib` identifies its rank,
span, and nullspace with their Mathlib analogues `Matrix.rank`,
`Submodule.span`, and `LinearMap.ker`. The proof recipes below use it.

# The echelon certificate
%%%
tag := "hex-row-reduce-echelon"
%%%

The elementary row operations ({name}`Hex.Matrix.rowSwap`,
{name}`Hex.Matrix.rowScale`, {name}`Hex.Matrix.rowAdd`) are documented in
{ref "hex-matrix"}[HexMatrix]. The reductions here compose them over a
field.

An echelon computation returns a certificate of how it reduced: the
rank, the reduced matrix, an invertible transform `T` with
`T * original = echelon`, and each row's pivot column.

{docstring Hex.Matrix.RowEchelonData}

Two predicates say when such a record is a genuine echelon or
reduced-echelon form. {name}`Hex.Matrix.IsEchelonForm` bundles the
conditions any echelon form shares: the transform equation, the
transform's invertibility, the rank bounds, and the staircase pivot
structure. {name}`Hex.Matrix.IsRowReduced` adds the two reduced-form
conditions: each pivot is one, and every entry above a pivot is zero.

# Gauss-Jordan reduction
%%%
tag := "hex-row-reduce-driver"
%%%

The driver is Gauss-Jordan elimination, returning a
{name}`Hex.Matrix.RowEchelonData` whose record satisfies the
reduced-form contract, with the transform equation and the rank read off
the result.

{docstring Hex.Matrix.rowReduce}

{docstring Hex.Matrix.rowReduce_transform_mul}

{docstring Hex.Matrix.rowReduce_isRowReduced}

{docstring Hex.Matrix.rowReduce_rank}

# Span and nullspace
%%%
tag := "hex-row-reduce-span"
%%%

From the reduced form we compute what a caller wants: the linear
combination of the rows, row-span membership with an explicit witness,
the Boolean span test, and a nullspace basis. Each has a soundness
theorem. The nullspace basis also has a completeness theorem.

{docstring Hex.Matrix.vecMul}

{docstring Hex.Matrix.spanCoeffs}

{docstring Hex.Matrix.spanCoeffs_sound}

{docstring Hex.Matrix.spanCoeffs_eq_none_iff}

{docstring Hex.Matrix.spanContains}

{docstring Hex.Matrix.spanContains_iff}

{docstring Hex.Matrix.nullspace}

{docstring Hex.Matrix.nullspaceBasisMatrix}

{docstring Hex.Matrix.nullspace_sound}

{docstring Hex.Matrix.nullspace_complete}

# Recipes
%%%
tag := "hex-row-reduce-recipes"
%%%

Task-oriented how-tos for the things callers reach for most. Each
executable recipe shows the idiomatic call and its result; where a
Mathlib correspondence theorem exists, a companion recipe then shows how
to *prove* the matching Mathlib fact by running the executable.

## How to find a basis for the kernel of a matrix
%%%
tag := "hex-row-reduce-recipe-kernel"
%%%

You have a matrix over a field and want a basis for its kernel: the
vectors `x` with `M * x = 0`. Build the matrix with the `#m[...]`
literal; {name}`Hex.Matrix.nullspaceBasisMatrix` returns the basis as
the columns of a matrix, one column per free (non-pivot) column of `M`.

```lean (name := kernelBasis)
open Hex Hex.Matrix

namespace HexRowReduceKernelRecipe

-- M has rank 1 (second row twice the first), 3 columns.
def M : Matrix Rat 2 3 := #m[1, 2, 3; 2, 4, 6]

-- The reduction reports rank 1, so nullity is 3 - 1 = 2.
#guard (Matrix.rowReduce M).rank = 1

-- The kernel basis, as the columns of a matrix.
#eval Matrix.nullspaceBasisMatrix M

-- The nullity is m - rank = 3 - 1 = 2.
#guard (Matrix.nullspace M).toArray.size = 2

end HexRowReduceKernelRecipe
```
```leanOutput kernelBasis
#m[-2, -3;
    1,  0;
    0,  1]
```

Each column is a basis vector: the kernel is spanned by `(-2, 1, 0)` and
`(-3, 0, 1)`. It is a genuine basis, not just a spanning set:
{name}`Hex.Matrix.nullspace_sound` says each vector is annihilated by
`M`, and {name}`Hex.Matrix.nullspace_complete` that every `x` with
`M * x = 0` is a combination of them.

## How to prove a fact about the Mathlib kernel by running Hex
%%%
tag := "hex-row-reduce-recipe-kernel-proof"
%%%

Everything above is purely executable: `#eval` runs the `Hex.Matrix`
routines and reads back concrete numbers. *This recipe crosses into
Mathlib.* `HexRowReduceMathlib` proves the executable rank,
span, and nullspace agree with Mathlib's noncomputable `Matrix.rank`,
`Submodule.span`, and `LinearMap.ker`, so you can settle a Mathlib goal
by running the executable and rewriting through a correspondence
theorem.

For the rank, {name}`HexMatrixMathlib.rank_eq` says the computed
{name}`Hex.Matrix.RowEchelonData.rank` equals `Matrix.rank (matrixEquiv M)`.
Rewriting with it turns a goal about the noncomputable Mathlib rank into
one about the executable rank, which the kernel evaluates directly.

```lean
open Hex Hex.Matrix HexMatrixMathlib

namespace HexRowReduceKernelProof

def A : _root_.Matrix (Fin 2) (Fin 3) Rat :=
  !![1, 2, 3; 2, 4, 6]

theorem rank_eq_one : A.rank = 1 := by
  rw [← matrixEquiv.apply_symm_apply A,
      ← rank_eq (rowReduce_isRowReduced _)]
  decide +kernel

end HexRowReduceKernelProof
```

`decide +kernel` runs the row reduction in the kernel and checks the
result. It is kernel-honest: the proof depends only on `propext`,
`Classical.choice`, and `Quot.sound`, never the compiler-trusting
`native_decide` (banned project-wide). For the kernel as a subspace, the
same pattern uses {name}`HexMatrixMathlib.nullspace_span_eq_ker`, whose
right-hand side is exactly the Mathlib `LinearMap.ker` of `M`'s
`mulVecLin`.

## How to test whether a vector is in the row span
%%%
tag := "hex-row-reduce-recipe-span"
%%%

You have a matrix and a vector and want to know whether the vector is a
linear combination of the rows. {name}`Hex.Matrix.spanContains` is the
decidable test; {name}`Hex.Matrix.spanCoeffs` returns the witnessing
coefficients when the answer is yes.

```lean (name := spanTest)
open Hex Hex.Matrix

namespace HexRowReduceSpanRecipe

def M : Matrix Rat 2 3 := #m[1, 2, 3; 2, 4, 6]

-- (1, 2, 3) is the first row, so it is in the row span.
#eval Matrix.spanContains M #v[1, 2, 3]

-- A vector off the rows' line is not.
#guard Matrix.spanContains M #v[1, 0, 0] = false

end HexRowReduceSpanRecipe
```
```leanOutput spanTest
true
```

## How to prove row-span membership in Mathlib by running Hex
%%%
tag := "hex-row-reduce-recipe-span-proof"
%%%

The Mathlib-side companion, like the kernel proof above, crosses into
Mathlib. {name}`HexMatrixMathlib.spanContains_iff_mem_span` turns the
executable {name}`Hex.Matrix.spanContains` test into membership in
Mathlib's `Submodule.span` of the rows, so a `Submodule.span` goal falls
to the same run-and-rewrite move.

```lean
open Hex Hex.Matrix HexMatrixMathlib

namespace HexRowReduceSpanProof

def A : _root_.Matrix (Fin 2) (Fin 3) Rat :=
  !![1, 2, 3; 2, 4, 6]
def w : Fin 3 → Rat := ![1, 2, 3]

theorem w_mem_span :
    w ∈ Submodule.span Rat (Set.range A.row) := by
  rw [← matrixEquiv.apply_symm_apply A,
      ← vectorEquiv.apply_symm_apply w,
      ← spanContains_iff_mem_span
          (rowReduce_isRowReduced (matrixEquiv.symm A)) _]
  decide +kernel

end HexRowReduceSpanProof
```

# Cross-references
%%%
tag := "hex-row-reduce-cross-references"
%%%

`HexRowReduce` depends only on {ref "hex-matrix"}[HexMatrix], using its
matrix type, arithmetic, and elementary operations.

* {ref "hex-determinant"}[HexDeterminant] and
  {ref "hex-bareiss"}[HexBareiss] handle the determinant; row reduction
  is the separate field-valued route for rank, span, and nullspace.
* `HexRowReduceMathlib` identifies the executable rank, span, and
  nullspace with Mathlib's linear algebra. `HexRowReduce` is
  Mathlib-free.
