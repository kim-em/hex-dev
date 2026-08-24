/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexMinPolyMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexMinPoly: matrix minimal polynomials" =>
%%%
tag := "hex-min-poly"
%%%

# Introduction
%%%
tag := "hex-min-poly-intro"
%%%

`HexMinPoly` computes minimal polynomials of dense square matrices over
fields. The computational layer is Mathlib-free and builds on
{ref "hex-matrix"}[HexMatrix], {ref "hex-row-reduce"}[HexRowReduce], and
{ref "hex-poly"}[HexPoly]. `HexMinPolyMathlib` connects the result to
Mathlib's `minpoly` and characteristic-polynomial theory.

For a matrix `A`, the minimal polynomial is the monic polynomial of least
degree that annihilates every vector. For one vector `v`, its order polynomial
is the monic polynomial of least degree that annihilates just `v`. The matrix
minimal polynomial is the least common multiple of the orders of the standard
basis vectors.

# Evaluation and Krylov sequences
%%%
tag := "hex-min-poly-krylov"
%%%

{docstring Hex.Matrix.evalVec}

`evalVec` uses Horner evaluation and never constructs a matrix power or a
polynomial-valued matrix. The Krylov operations expose the successive vectors
used to discover a first dependency.

{docstring Hex.Matrix.krylovVec}

{docstring Hex.Matrix.krylovRows}

{docstring Hex.Matrix.krylovMat}

`krylovRows A v r` computes each new row from the preceding one, sharing all
matrix-vector products. `krylovMat` is the matrix view of the same sequence.

```lean
open Hex
open scoped Hex

namespace HexMinPolyChapterExample

def A : Matrix Rat 2 2 := #m[0, 1; 0, 0]
def v : Vector Rat 2 := #v[0, 1]

#guard A.krylovVec v 1 == #v[1, 0]
#guard A.krylovVec v 2 == #v[0, 0]

end HexMinPolyChapterExample
```

{docstring Hex.Matrix.krylovDeg}

{docstring Hex.Matrix.krylovCoeffs?}

{docstring Hex.Matrix.dependencyPoly}

If the dependency coefficients are `c₀, ..., c_(d-1)`, the resulting
polynomial is `x^d - Σ c_j x^j`. The first `d` rows are independent; their
right inverse later becomes the minimality witness in a certificate.

# Vector orders and the matrix polynomial
%%%
tag := "hex-min-poly-api"
%%%

{docstring Hex.Matrix.vecMinPoly}

{docstring Hex.Matrix.vecMinPoly_monic}

{docstring Hex.Matrix.evalVec_vecMinPoly}

{docstring Hex.Matrix.vecMinPoly_dvd}

These three laws say that the computed vector order is monic, annihilates the
given vector, and divides every other annihilator of that vector.

{docstring Hex.Matrix.minPoly}

{docstring Hex.Matrix.minPoly_monic}

{docstring Hex.Matrix.evalVec_minPoly}

{docstring Hex.Matrix.minPoly_dvd_iff}

The last equivalence is the complete user-facing contract: divisibility by
the minimal polynomial is exactly the property of annihilating all vectors.

```lean
open Hex
open scoped Hex

namespace HexMinPolyResultExample

def A : Matrix Rat 2 2 := #m[0, 1; 0, 0]
def v : Vector Rat 2 := #v[0, 1]

#guard A.vecMinPoly v == #p[0, 0, 1]
#guard A.minPoly == #p[0, 0, 1]
example : A.evalVec A.minPoly v = 0 :=
  Hex.Matrix.evalVec_minPoly A v

end HexMinPolyResultExample
```

Closed forms cover the empty matrix, positive-dimensional zero and identity
matrices, one-by-one matrices, zero vectors, and nonzero eigenvectors.

{name Hex.Matrix.minPoly_empty}`Hex.Matrix.minPoly_empty` states that the
empty matrix has minimal polynomial `1`.

{docstring Hex.Matrix.minPoly_zero}

{docstring Hex.Matrix.minPoly_identity}

{docstring Hex.Matrix.vecMinPoly_eigen}

# Checkable certificates
%%%
tag := "hex-min-poly-certificates"
%%%

`Hex.Matrix.OrderCert` records an order polynomial, its degree, and a right
inverse of the independent Krylov prefix. `Hex.Matrix.LcmStep` records
common-factor, cofactor, and Bézout identities for one LCM step.
`Hex.Matrix.MinPolyCert` contains one order witness and one LCM witness for
every standard basis vector.

{docstring Hex.Matrix.checkRightInverse}

{docstring Hex.Matrix.MinPolyCert.check}

{docstring Hex.Matrix.MinPolyCert.check_sound}

The checker uses matrix-vector products and polynomial ring identities. A
successful certificate proves monicity, annihilation on every vector, and
divisibility into every other annihilator.

{docstring Hex.Matrix.minPolyCert}

{docstring Hex.Matrix.minPolyCert_check}

```lean
open Hex
open scoped Hex

namespace HexMinPolyCertificateExample

def A : Matrix Rat 2 2 := #m[0, 1; 0, 0]

example : (A.minPolyCert).check A = true :=
  Hex.Matrix.minPolyCert_check A

end HexMinPolyCertificateExample
```

# Complexity and validation
%%%
tag := "hex-min-poly-validation"
%%%

One dense matrix-vector product costs `O(n²)` field operations. Building a
Krylov sequence and reducing its matrix each cost `O(n³)`. Repeating this for
the standard basis gives the deterministic matrix algorithm a conservative
`O(n⁴)` field-operation bound.

Required conformance tests exercise the individual Krylov and dependency
operations, valid certificates, and deliberately corrupted right-inverse,
order, Bézout, and monicity witnesses. Integer and rational fixture results
are checked coefficient-for-coefficient against FLINT. Benchmarks separate
evaluation, Krylov construction, vector orders, matrix minimal polynomials,
certificate production, and certificate checking, with FLINT and PARI as
informational comparators.

# The Mathlib correspondence
%%%
tag := "hex-min-poly-mathlib"
%%%

{docstring HexMinPolyMathlib.equiv_minPoly}

{docstring HexMinPolyMathlib.vectorEquiv_evalVec}

{docstring HexMinPolyMathlib.vecMinPoly_dvd_iff}

The bridge also identifies executable LCM with Mathlib's normalized LCM and
derives the characteristic-polynomial degree bound.

{docstring HexMinPolyMathlib.equiv_lcm}

{docstring HexMinPolyMathlib.minPoly_dvd_charPoly}

{docstring HexMinPolyMathlib.degree?_minPoly_le}

Finally, the executable minimal polynomial has the expected invariance laws.

{docstring HexMinPolyMathlib.minPoly_transpose}

{docstring HexMinPolyMathlib.minPoly_conj}
