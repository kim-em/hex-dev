/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexPolySmithMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexPolySmith: polynomial Smith normal form" =>
%%%
tag := "hex-poly-smith"
%%%

# Introduction
%%%
tag := "hex-poly-smith-intro"
%%%

`HexPolySmith` computes Smith normal form for dense matrices over `F[x]`. Its
nonzero diagonal entries are monic and form a divisibility chain, so they are
the invariant factors of the matrix and describe the module presented by its
rows. The algorithm, matrices, and dense polynomials are Mathlib-free.

The companion `HexPolySmithMathlib` transports the result to Mathlib's
`Polynomial F`, module-basis, quotient, and rational-function rank APIs.

# Smith data and entry points
%%%
tag := "hex-poly-smith-api"
%%%

The full record contains the rank, nonzero diagonal, left and right change-of-
basis matrices, and explicit inverses for both transformations.

{docstring Hex.PolyMatrix.SmithData}

Use {name}`Hex.PolyMatrix.snf` when only the diagonal matrix is needed. The
transform-free projections {name}`Hex.PolyMatrix.snfRank` and
{name}`Hex.PolyMatrix.invariantFactors` avoid accumulating the four
transformation matrices. Use {name}`Hex.PolyMatrix.snfData` when a basis change
or certificate is required.

{docstring Hex.PolyMatrix.snf}

{docstring Hex.PolyMatrix.snfRank}

{docstring Hex.PolyMatrix.snfData}

{docstring Hex.PolyMatrix.invariantFactors}

Diagonal input has convenience wrappers around the same certified reduction.

{docstring Hex.PolyMatrix.snfDiagonal}

{docstring Hex.PolyMatrix.snfDiagonalData}

# Module structure and solving
%%%
tag := "hex-poly-smith-structure"
%%%

`moduleStructure` returns the free rank and the nonunit torsion factors of the
presented module. `quotientOrder` is the monic generator of the zeroth Fitting
ideal, or zero when the quotient has a free summand.

{docstring Hex.PolyMatrix.moduleStructure}

{docstring Hex.PolyMatrix.quotientOrder}

The solver decides and constructs row-vector solutions of `x * A = b`. It
transforms the right-hand side by the right basis change, solves the diagonal
system, and maps the solution back with the left basis change.

{docstring Hex.PolyMatrix.solve}

# Worked example
%%%
tag := "hex-poly-smith-example"
%%%

The following example is elaborated with the manual. Its diagonal entries
already form the chain `x ∣ x²`, so the Smith form is unchanged.

```lean
open Hex Hex.PolyMatrix

namespace HexPolySmithChapterExample

private def x : DensePoly Rat := DensePoly.ofList [0, 1]

private def A : Matrix (DensePoly Rat) 2 2 :=
  #m[x, 0; 0, x * x]

#guard snfRank A = 2
#guard snf A == A
#guard (invariantFactors A).toList == [x, x * x]
#guard quotientOrder A == x * x * x

private def witness : Vector (DensePoly Rat) 2 :=
  #v[x + 1, 2]
private def b : Vector (DensePoly Rat) 2 :=
  Hex.Matrix.vecMul witness A

#guard solve A b == some witness

end HexPolySmithChapterExample
```

# Certificates and correctness
%%%
tag := "hex-poly-smith-correctness"
%%%

The logical contract packages the inverse identities, transformed-input
identity, rank bounds, monicity, and divisibility chain.

{docstring Hex.PolyMatrix.IsSNF}

The general algorithm satisfies that contract, and the direct certificate
checker is sound for independently supplied data.

{docstring Hex.PolyMatrix.snfData_isSNF}

{docstring Hex.PolyMatrix.snfCert}

{docstring Hex.PolyMatrix.snfCert_sound}

For large polynomial products, an evaluation certificate can check the
identity at scalar points. Its soundness theorem makes the separation and
degree hypotheses explicit; small fields do not silently obtain enough
points.

{docstring Hex.PolyMatrix.mulEqCertAt}

{docstring Hex.PolyMatrix.mulEqCertAt_sound}

# The Mathlib correspondence
%%%
tag := "hex-poly-smith-mathlib"
%%%

The bridge maps entries to `Polynomial F` and preserves matrix multiplication.

{docstring HexPolySmithMathlib.polyMatrixEquiv}

{docstring HexPolySmithMathlib.polyMatrixEquiv_mul}

It constructs Mathlib's simultaneous Smith-basis structure and supplements it
with the invariant-factor divisibility chain.

{docstring HexPolySmithMathlib.smithNormalForm}

{docstring HexPolySmithMathlib.smithNormalForm_chain}

The quotient decomposition separates its free coordinates from the cyclic
torsion factors, while the rank theorem extends scalars to the fraction field
`F(x)`.

{docstring HexPolySmithMathlib.quotientEquiv}

{docstring HexPolySmithMathlib.rank_eq_ratFunc_rank}

# Cross-references
%%%
tag := "hex-poly-smith-cross-references"
%%%

`HexPolySmith` uses {ref "hex-poly"}[HexPoly] for dense Euclidean polynomial
arithmetic, {ref "hex-matrix"}[HexMatrix] for matrix operations, and
{ref "hex-determinant"}[HexDeterminant] for determinantal-divisor arguments.
The characteristic-matrix application and rational canonical form belong to a
separate downstream library.
