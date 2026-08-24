/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexCharPolyMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexCharPoly: characteristic polynomials" =>
%%%
tag := "hex-char-poly"
%%%

# Introduction
%%%
tag := "hex-char-poly-intro"
%%%

Released as
[hex-char-poly](https://github.com/leanprover/hex-char-poly), with the
Mathlib correspondence in
[hex-char-poly-mathlib](https://github.com/leanprover/hex-char-poly-mathlib).

`HexCharPoly` computes the characteristic polynomial
`det (xI - A)` of a dense square matrix with the division-free
Samuelson--Berkowitz algorithm. The computational library is
Mathlib-free and works over every commutative ring with decidable
equality. Its only Hex dependencies are
{ref "hex-matrix"}[HexMatrix] and {ref "hex-poly"}[HexPoly].

The algorithm does no division or pivoting. It therefore works without
assuming that nonzero elements are invertible, and has no
failure-producing branch. Its `O(n^4)` ring-operation cost makes it a
portable certified implementation rather than a replacement for a
specialized characteristic-polynomial routine on very large matrices.

# Representation and public API
%%%
tag := "hex-char-poly-api"
%%%

{name}`Hex.Matrix.berkowitz` returns `n + 1` coefficients in descending
degree order. Entry zero is the coefficient of `x^n`; entry `n` is the
constant coefficient.

{docstring Hex.Matrix.berkowitz}

The user-facing {name}`Hex.Matrix.charPoly` reverses that vector and
stores it as a normalized {name}`Hex.DensePoly`, whose coefficients are
in ascending order.

{docstring Hex.Matrix.charPoly}

The result is monic, including over the zero ring. Over a nontrivial
ring it has stored size `n + 1` and degree `n`.

{docstring Hex.Matrix.charPoly_monic}

{docstring Hex.Matrix.size_charPoly}

{docstring Hex.Matrix.degree?_charPoly}

The library also provides the matrix trace and Horner evaluation of a
dense polynomial at a square matrix.

{docstring Hex.Matrix.trace}

{docstring Hex.Matrix.evalMatrix}

# The Berkowitz recursion
%%%
tag := "hex-char-poly-berkowitz"
%%%

The recursion grows trailing principal blocks. At one step, write the
new block as `[[a, R], [C, B]]`. The first column of the lower-triangular
Toeplitz step is

`1, -a, -(R C), -(R B C), ..., -(R B^(k-1) C)`.

Successive vectors `B^j C` are computed iteratively. Multiplying the
Toeplitz matrix by the coefficient vector for `B` produces the
coefficient vector for the new bordered block.

{docstring Hex.Matrix.berkowitzColumn}

{docstring Hex.Matrix.berkowitzStep}

The leading coefficient stays one at every intermediate step, and the
coefficient of `x^(n-1)` in the final polynomial is the negated trace.

{docstring Hex.Matrix.berkowitzAux_zero}

{docstring Hex.Matrix.coeff_charPoly_pred}

# Computing certified concrete results
%%%
tag := "hex-char-poly-tactic"
%%%

For a closed `Hex.Matrix Int n n`, `char_poly A` is a term containing
the computed polynomial and a proof that it equals
{name}`Hex.Matrix.charPoly` applied to `A`. Bare `char_poly` closes a direct equality
in either orientation.

```lean
open Hex
open scoped Hex

namespace HexCharPolyChapterExample

private def A : Hex.Matrix Int 2 2 :=
  #m[1, 2; 3, 4]

private def result := char_poly A

example : result.poly = #p[-2, -5, 1] := rfl

example : Hex.Matrix.charPoly A = #p[-2, -5, 1] := by
  char_poly

example : #p[-2, -5, 1] = Hex.Matrix.charPoly A := by
  char_poly

example : True := by
  char_poly A
  have _ : Hex.Matrix.charPoly A = poly := charPoly_eq
  trivial

end HexCharPolyChapterExample
```

The explicit tactic form introduces a transparent `poly` local
definition and a `charPoly_eq` hypothesis. This is useful when the
computed polynomial is an intermediate fact rather than the goal.

Importing `HexCharPolyMathlib` adds the same interface for a closed
`Matrix (Fin n) (Fin n) Int`. Direct goals use ordinary Mathlib
polynomial notation.

```lean
open Matrix Polynomial

namespace HexCharPolyMathlibChapterExample

private def A : Matrix (Fin 2) (Fin 2) Int :=
  !![1, 2; 3, 4]

example : A.charpoly = X ^ 2 - 5 * X - 2 := by
  char_poly

example : X ^ 2 - 5 * X - 2 = A.charpoly := by
  char_poly

example : True := by
  char_poly A
  have _ : A.charpoly = poly := charPoly_eq
  trivial

end HexCharPolyMathlibChapterExample
```

The term and tactic currently support integer matrices only. The
matrix, its dimension, and a polynomial appearing in a direct equality
must be closed and definitionally transparent. Mathlib polynomial goals
may use `X`, `C`, integer numerals, addition, subtraction,
multiplication, negation, and natural-literal powers; transparent named
definitions built from those forms are unfolded.

Compiled evaluation discovers the coefficients and intermediate
values. The emitted term separately certifies the scalar dot products,
matrix-vector products, Berkowitz steps, and final coefficients. For a
Mathlib matrix it additionally certifies every materialized entry and
then uses the correspondence theorem below. The compiled evaluator is
not trusted, and Mathlib's noncomputable `Matrix.charpoly` is not
evaluated.

# The Mathlib correspondence
%%%
tag := "hex-char-poly-mathlib"
%%%

`HexCharPolyMathlib` identifies the executable polynomial with
Mathlib's {name _root_.Matrix.charpoly}`Matrix.charpoly` after
transporting both the matrix and polynomial through their equivalences.

{docstring HexCharPolyMathlib.equiv_charPoly}

This correspondence supplies the determinant interpretation of
evaluation and Cayley--Hamilton without adding Mathlib or a determinant
dependency to the computational package.

{docstring HexCharPolyMathlib.eval_charPoly}

{docstring HexCharPolyMathlib.evalMatrix_charPoly}

The constant coefficient is the signed determinant, and transposition
and conjugation by an explicitly supplied inverse preserve the
polynomial.

{docstring HexCharPolyMathlib.coeff_zero_charPoly}

{docstring HexCharPolyMathlib.charPoly_transpose}

{docstring HexCharPolyMathlib.charPoly_conj}

# Cross-references
%%%
tag := "hex-char-poly-cross-references"
%%%

* {ref "hex-matrix"}[HexMatrix] supplies the dense matrix type and
  arithmetic used by the recursion.
* {ref "hex-poly"}[HexPoly] supplies the normalized dense polynomial
  representation.
* {ref "hex-determinant"}[HexDeterminant] supplies the Mathlib-free
  Leibniz determinant used to state the evaluation law in the
  correspondence package.
* {ref "hex-bareiss"}[HexBareiss] is the fraction-free executable route
  for integer determinants; it computes a determinant rather than the
  complete characteristic polynomial.
