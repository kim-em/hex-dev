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

`HexRowReduce` is the executable row-reduction stack over the
{ref "hex-matrix"}[HexMatrix] dense core: Gauss-Jordan reduction to
reduced row echelon form over a field, together with the row-span and
nullspace computations built on it. It depends only on `HexMatrix`.

The reduction returns more than a reduced matrix: it returns a
certificate — the rank, the reduced form, the accumulated invertible
transform, and the pivot columns — and the linear-algebra readers a
caller actually wants are derived from that certificate with soundness
(and, for the nullspace, completeness) theorems tying the executable
answer back to the matrix. This chapter walks the echelon certificate,
the `rowReduce` driver, and the span and nullspace readers, and closes
with a worked example checked when the chapter is built.

`HexRowReduce` is Mathlib-free. The identification of its rank, span, and
nullspace with Mathlib's linear-algebra theory lives in the forthcoming
`HexRowReduceMathlib` bridge.

# The echelon certificate
%%%
tag := "hex-row-reduce-echelon"
%%%

The elementary row operations ({name}`Hex.Matrix.rowSwap`,
{name}`Hex.Matrix.rowScale`, {name}`Hex.Matrix.rowAdd`) are documented
with the {ref "hex-matrix"}[matrix core]; the reductions here compose
them over a field, where division by a pivot is available.

An echelon computation returns its result packaged with a certificate of
how it got there: the rank, the reduced matrix, the accumulated
invertible row-operation transform `T` with `T * original = echelon`,
and the pivot column of each row.

{docstring Hex.Matrix.RowEchelonData}

Two predicates capture what it means for such a record to be a genuine
echelon or reduced-echelon form. {name}`Hex.Matrix.IsEchelonForm` bundles
the conditions shared by any echelon form — the transform equation, the
transform's invertibility, the rank bounds, and the staircase pivot
structure. {name}`Hex.Matrix.IsRowReduced` extends it with the two
reduced-form conditions: each pivot is one, and every entry above a
pivot is zero.

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

On top of the reduced form sit the linear-algebra readers a caller
actually wants: the linear combination of the rows, membership in the
row span with an explicit witness, the boolean span test, and a basis
for the nullspace — each with a soundness theorem, and the nullspace
basis additionally with a completeness theorem.

{docstring Hex.Matrix.rowCombination}

{docstring Hex.Matrix.spanCoeffs}

{docstring Hex.Matrix.spanCoeffs_sound}

{docstring Hex.Matrix.spanContains}

{docstring Hex.Matrix.nullspace}

{docstring Hex.Matrix.nullspaceBasisMatrix}

{docstring Hex.Matrix.nullspace_sound}

{docstring Hex.Matrix.nullspace_complete}

# Worked example
%%%
tag := "hex-row-reduce-worked"
%%%

The block below builds the `2 × 3` rational matrix with rows `(1, 2, 3)`
and `(2, 4, 6)`. The second row is twice the first, so the rank is `1`,
and the vector `(1, 2, 3)` — the first row itself — lies in the row
span. Every `#guard` is checked when the chapter is built.

```lean
open Hex Hex.Matrix

namespace HexRowReduceChapterExample

-- M = [[1,2,3],[2,4,6]], rank 1 (rows dependent).
private def M : Matrix Rat 2 3 :=
  Matrix.ofFn fun i j => (i + 1) * (j + 1)

-- The reduction reports rank 1.
#guard (Matrix.rowReduce M).rank = 1

-- (1, 2, 3) is the first row, hence in the row span.
private def v : Vector Rat 3 := Vector.ofFn fun j => j + 1

#guard Matrix.spanContains M v = true

end HexRowReduceChapterExample
```

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

You have a matrix over a field and want a basis for its kernel — the
vectors `x` with `M * x = 0`. Build the matrix with the `#m[...]`
literal and read the basis off {name}`Hex.Matrix.nullspace`, which
returns one vector per free (non-pivot) column.

```lean (name := kernelBasis)
open Hex Hex.Matrix

namespace HexRowReduceKernelRecipe

-- M has rank 1 (second row twice the first), 3 columns.
def M : Matrix Rat 2 3 := #m[1, 2, 3; 2, 4, 6]

-- The kernel basis, one vector per free column. Collected as the rows of a
-- matrix (`ofRows`) so it prints in copy-pasteable `#m[...]` form.
#eval Matrix.ofRows (Matrix.nullspace M)

-- The nullity is m - rank = 3 - 1 = 2.
#guard (Matrix.nullspace M).toArray.size = 2

end HexRowReduceKernelRecipe
```
```leanOutput kernelBasis
#m[-2, 1, 0;
   -3, 0, 1]
```

Each row is a basis vector: the kernel is spanned by
`(-2, 1, 0)` and `(-3, 0, 1)`. The result is a genuine basis, not just a
spanning set — every returned vector is annihilated by `M`
({name}`Hex.Matrix.nullspace_sound`), and every `x` with `M * x = 0` is
a combination of them ({name}`Hex.Matrix.nullspace_complete`).

## How to prove a fact about the Mathlib kernel by running Hex
%%%
tag := "hex-row-reduce-recipe-kernel-proof"
%%%

Everything above is purely executable: `#eval` runs the `Hex.Matrix`
routines and reads back concrete numbers. *This recipe crosses into
Mathlib.* The `HexRowReduceMathlib` bridge proves the executable rank,
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

def M : Matrix Rat 2 3 := #m[1, 2, 3; 2, 4, 6]

theorem rank_eq_one :
    _root_.Matrix.rank (matrixEquiv M) = 1 := by
  rw [← rank_eq (rowReduce_isRowReduced M)]
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

If a matrix is large enough that kernel reduction stalls, `decide_cbv`
is a drop-in fallback — also kernel-honest, but roughly forty times
slower on the matrices measured here.

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

def M : Matrix Rat 2 3 := #m[1, 2, 3; 2, 4, 6]
def v : Vector Rat 3 := #v[1, 2, 3]

theorem v_mem_span :
    vectorEquiv v ∈ Submodule.span Rat
      (Set.range (_root_.Matrix.row (matrixEquiv M))) := by
  rw [← spanContains_iff_mem_span
        (rowReduce_isRowReduced M)]
  decide +kernel

end HexRowReduceSpanProof
```

# Cross-references
%%%
tag := "hex-row-reduce-cross-references"
%%%

`HexRowReduce` is the row-reduction layer of the linear-algebra stack:

* It depends only on {ref "hex-matrix"}[HexMatrix] — the matrix type,
  its arithmetic, and the elementary operations it composes.
* The {ref "hex-determinant"}[HexDeterminant] and
  {ref "hex-bareiss"}[HexBareiss] libraries handle the determinant; row
  reduction is the separate field-valued route for rank, span, and
  nullspace.
* `HexRowReduceMathlib` is the correspondence library identifying the
  executable rank, span, and nullspace with Mathlib's linear algebra.
  The Mathlib dependency lives entirely on that side of the boundary;
  `HexRowReduce` itself is Mathlib-free.
