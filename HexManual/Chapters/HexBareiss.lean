/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexBareissMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexBareiss: the fraction-free integer determinant" =>
%%%
tag := "hex-bareiss"
%%%

# Introduction
%%%
tag := "hex-bareiss-intro"
%%%

Released as [hex-bareiss](https://github.com/leanprover/hex-bareiss), with
the Mathlib correspondence in
[hex-bareiss-mathlib](https://github.com/leanprover/hex-bareiss-mathlib).

`HexBareiss` is the executable fraction-free Bareiss determinant of a
dense integer matrix: a Gaussian elimination in which every intermediate
entry stays an exact integer because each update divides *exactly* by
the previous pivot. It runs in cubic time and never leaves the integers,
so it avoids both the factorial blow-up of the Leibniz
{ref "hex-determinant"}[determinant] and the denominators of ordinary
Gaussian elimination. It builds on {ref "hex-matrix"}[HexMatrix] and the
{ref "hex-determinant"}[HexDeterminant] Leibniz determinant (the
specification it is checked against).

`HexBareiss` is Mathlib-free. The theorem identifying the Bareiss
determinant with the Leibniz determinant (and hence with Mathlib's
`Matrix.det`), via the Desnanot-Jacobi invariant, is the
{ref "hex-bareiss-mathlib"}[last section].

# The elimination record
%%%
tag := "hex-bareiss-record"
%%%

An elimination pass returns a small record: the terminal matrix, the
number of row swaps performed during pivoting, and an optional record of
the first step at which a zero pivot with no replacement row was found
(the signal that the matrix is singular).

{docstring Hex.Matrix.BareissData}

The sign contributed by the row swaps and the encoded determinant are
read off that record. A recorded singular step encodes determinant zero.
Otherwise the determinant is the last diagonal entry of the terminal
matrix with the swap sign applied.

{docstring Hex.Matrix.BareissData.sign}

{docstring Hex.Matrix.BareissData.det}

# Entry points
%%%
tag := "hex-bareiss-entry"
%%%

The public entry points run the row-pivoting elimination.
{name}`Hex.Matrix.bareissData` returns the full record.
{name}`Hex.Matrix.bareiss` returns just the integer determinant. The
no-pivot variants skip the pivot search, for inputs whose leading pivots
are already nonzero.

{docstring Hex.Matrix.bareissData}

{docstring Hex.Matrix.bareiss}

{docstring Hex.Matrix.bareissNoPivotData}

{docstring Hex.Matrix.bareissNoPivot}

The division at each step is `Int.divExact` (a GMP-backed
`mpz_divexact`), which is always exact and carries its divisibility
proof. The bordered minors are the intermediate determinants the
correctness proof uses as its elimination invariant.

{docstring Hex.Matrix.borderedMinor}

# Structural theorems
%%%
tag := "hex-bareiss-theorems"
%%%

`HexBareiss` proves the structural facts about the elimination: that the
packaged record is the pivot loop's final state packaged as determinant
data, and that the public {name}`Hex.Matrix.bareiss` value agrees with
the determinant encoded by {name}`Hex.Matrix.bareissData`. It does not prove that the Bareiss
determinant equals the Leibniz {name}`Hex.Matrix.det`. That
identification is in `HexBareissMathlib`. Within `HexBareiss` itself the
agreement is checked at build time by value-level conformance fixtures: a
fixed bank of matrices on which `Hex.Matrix.bareiss M = Hex.Matrix.det M`
is verified.

{docstring Hex.Matrix.bareissData_eq_finish_pivotLoop}

{docstring Hex.Matrix.bareiss_eq_bareissData_det}

# Worked example
%%%
tag := "hex-bareiss-worked"
%%%

The block below builds the integer matrix with rows `(2, 0, 1)`,
`(1, 3, 2)`, and `(0, 1, 1)`, whose determinant is `3`. The Bareiss
route agrees with the Leibniz {ref "hex-determinant"}[determinant] on it,
the identity has determinant one, and a matrix with a dependent row pair
is singular.

```lean
open Hex Hex.Matrix

namespace HexBareissChapterExample

-- A = [[2, 0, 1], [1, 3, 2], [0, 1, 1]], det = 3.
private def A : Hex.Matrix Int 3 3 :=
  #m[2, 0, 1; 1, 3, 2; 0, 1, 1]

-- The Bareiss determinant is 3, agreeing with Leibniz.
#guard bareiss A = 3
#guard bareiss A = det A

-- The packaged record reads off the same determinant.
#guard (bareissData A).det = 3

-- The identity has determinant one.
#guard bareiss (Hex.Matrix.identity (R := Int) 3) = 1

-- S = [[1, 2], [2, 4]]: dependent rows, so singular.
private def S : Hex.Matrix Int 2 2 := #m[1, 2; 2, 4]

#guard bareiss S = 0

end HexBareissChapterExample
```

# The Mathlib correspondence
%%%
tag := "hex-bareiss-mathlib"
%%%

Everything above is executable and Mathlib-free. `HexBareissMathlib`
connects it to Mathlib. Its headline theorem is that the fraction-free
Bareiss determinant equals the Leibniz {ref "hex-determinant"}[determinant]
on integer square matrices, so the cubic-time route and the
specification agree outright.

{docstring HexMatrixMathlib.bareiss_eq_det}

Composed with the {ref "hex-determinant-mathlib"}[determinant
correspondence], this also identifies the Bareiss determinant with
Mathlib's `Matrix.det`.

{docstring HexMatrixMathlib.bareissDet_eq_det}

# Cross-references
%%%
tag := "hex-bareiss-cross-references"
%%%

`HexBareiss` is the fast route to an exact integer determinant.

* It depends on {ref "hex-matrix"}[HexMatrix] for the matrix type and on
  {ref "hex-determinant"}[HexDeterminant] for the Leibniz `det` it uses
  as its specification.
* `HexBareissMathlib` proves the Bareiss determinant equals the Leibniz
  determinant (and hence Mathlib's), via the Desnanot-Jacobi invariant.
  `HexBareiss` itself is Mathlib-free.
