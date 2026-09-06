/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexNumberFieldMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexNumberField: exact algebraic numbers" =>
%%%
tag := "hex-number-field"
%%%

# Introduction
%%%
tag := "hex-number-field-intro"
%%%

`HexNumberField` computes with algebraic numbers exactly. An algebraic number
is stored as its minimal polynomial over the integers together with a
certified disc that singles out one complex root: `√2 + √3` is the polynomial
`X⁴ − 10X² + 1` and a small disc around `3.146`. Addition, multiplication,
inversion and powers return numbers in the same normal form, and equality is a
comparison of that data. There are no floating-point numbers anywhere. The
discs have dyadic rational centres and radii, and each carries a certificate,
checked by ordinary evaluation, that it contains exactly one root.

Two cheaper forms sit beside the canonical one. An {name}`Hex.AlgebraicRoot`
is a root of some squarefree integer polynomial that need not be minimal: the
sum of two roots is a root of a resultant, and factoring that resultant is
postponed until a canonical answer is requested with
{name}`Hex.AlgebraicRoot.exact`. A {name}`Hex.QAdjoin` is the field `ℚ(x)` for
one fixed root `x` of an irreducible polynomial, with elements written as
rational coordinates in the power basis; arithmetic there is polynomial
arithmetic modulo the defining polynomial and involves no root isolation at
all. Roots of polynomials whose coefficients are themselves algebraic numbers
are found with {name}`Hex.AlgebraicPoly.roots`.

The correspondence library `HexNumberFieldMathlib` interprets every
representation in `ℂ`. It proves that the interpretation of canonical numbers
is injective, that each executable operation computes the corresponding
complex operation, and it installs a `Field` instance on
{name}`Hex.AlgebraicNumber` whose operations are the executable ones. The
place to start is {name}`Hex.ZPoly.algebraicRoots`, which turns an integer
polynomial into its roots as canonical algebraic numbers.

{docstring Hex.AlgebraicNumber}

{docstring Hex.ZPoly.algebraicRoots}

# Square roots and the golden ratio
%%%
tag := "hex-number-field-examples"
%%%

`#p[a₀, a₁, …]` writes an integer polynomial by its coefficients in increasing
degree, so `#p[-2, 0, 1]` is `X² − 2`. Its roots come back real first and in
increasing order, so index `1` is `+√2`:

```lean
open Hex

namespace HexNumberFieldChapter

def sqrt2 : AlgebraicNumber :=
  (ZPoly.algebraicRoots #p[-2, 0, 1])[1]!
def sqrt3 : AlgebraicNumber :=
  (ZPoly.algebraicRoots #p[-3, 0, 1])[1]!

#guard (ZPoly.algebraicRoots #p[-2, 0, 1]).size = 2
#guard sqrt2 * sqrt2 = 2
#guard (sqrt2 + sqrt3).p = #p[1, 0, -10, 0, 1]
#guard (sqrt2 + sqrt3)⁻¹ = sqrt3 - sqrt2
```

The field `p` of a canonical number is its minimal polynomial, so the third
check is the classical fact that `√2 + √3` has minimal polynomial
`X⁴ − 10X² + 1`, and the fourth is `1 / (√2 + √3) = √3 − √2`. Equality of
canonical numbers is decidable. Without the Mathlib companion, compare with
`==`, the executable test; with it, `=` is available too, because the
companion proves that the test is correct. Printing a number shows that
polynomial and twelve decimals of a certified approximation:

```lean (name := sqrtSumEval)
#eval sqrt2 + sqrt3
```
```leanOutput sqrtSumEval
root of X^4 - 10*X^2 + 1 near 3.146264369941
```

The golden ratio is the positive root of `X² − X − 1`. Its defining identity,
its reciprocal, and the tenth Lucas number all fall out of decidable equality:

```lean
def φ : AlgebraicNumber :=
  (ZPoly.algebraicRoots #p[-1, -1, 1])[1]!

#guard φ * φ = φ + 1
#guard φ⁻¹ = φ - 1
-- φ¹⁰ + φ⁻¹⁰ is the Lucas number L₁₀ = 123, so φ¹⁰ is a
-- root of X² − 123X + 1.
#guard (φ ^ (10 : Nat)).p = #p[1, -123, 1]
```

# Lazy roots and exactification
%%%
tag := "hex-number-field-lazy"
%%%

Canonical arithmetic is built on a cheaper intermediate form. Adding two lazy
roots builds the resultant whose roots are all sums of a root of the first
polynomial with a root of the second, and isolates the one that is the actual
sum; nothing is factored. The sum of `√2` with itself is a root of
`X³ − 8X`, whose three roots `0`, `±2√2` are the sums of pairs of conjugates.
Requesting the canonical form factors that polynomial and keeps `X² − 8`:

```lean
def lazySum : AlgebraicRoot :=
  sqrt2.toRoot.add sqrt2.toRoot

#guard lazySum.p = #p[0, -8, 0, 1]
#guard lazySum.exact.p = #p[-8, 0, 1]

def lazyProduct : AlgebraicRoot :=
  sqrt2.toRoot.mul sqrt2.toRoot

#guard lazyProduct.p = #p[-4, 0, 1]
#guard lazyProduct.exact.p = #p[-2, 1]
#guard lazyProduct.exact = 2
```

A chain of lazy operations therefore costs a chain of resultants and one
factorization at the end, instead of a factorization at every step. Canonical
numbers use the same route and exactify each result, which is what makes their
equality decidable.

{docstring Hex.AlgebraicRoot.exact}

# Polynomials with algebraic coefficients
%%%
tag := "hex-number-field-roots"
%%%

An {name}`Hex.AlgebraicPoly` has canonical algebraic numbers as coefficients;
trailing coefficients equal to zero are dropped by value, not by
representation. Its roots are lazy roots with multiplicities: the polynomial
`X² − √2` has the two real fourth roots of `2`, each simple, each with minimal
polynomial `X⁴ − 2`.

```lean
/-- The finite root list; empty for the zero polynomial. -/
def finiteRoots : RootSet → Array RootCount
  | .finite rs => rs
  | .all => #[]

def quarticRoots : Array RootCount :=
  finiteRoots
    (AlgebraicPoly.ofArray #[-sqrt2, 0, 1]).roots

#guard quarticRoots.size = 2
#guard quarticRoots.all fun r =>
  r.multiplicity = 1 &&
    r.root.exact.p = #p[-2, 0, 0, 0, 1]
```

The `.all` case of a root set is the zero polynomial, every number being a
root of it.

{docstring Hex.AlgebraicPoly.roots}

# A fixed field: ℚ(∛2)
%%%
tag := "hex-number-field-fixed"
%%%

If you are working in a fixed number field, use {name}`Hex.QAdjoin`. Any
algebraic number converts into its own field with
{name}`Hex.AlgebraicNumber.toQAdjoin`. Arithmetic and equality are efficient
there, since an element is just a rational polynomial in the generator
reduced modulo its minimal polynomial, and inverses are calculated with
extended gcds.

```lean
def cbrt2 : AlgebraicNumber :=
  (ZPoly.algebraicRoots #p[-2, 0, 0, 1])[0]!

def c : QAdjoin cbrt2.p cbrt2.x := cbrt2.toQAdjoin

#guard c ^ 3 = 2
#guard c⁻¹ = c * c / 2
#guard c.toAlgebraicNumber cbrt2.rep cbrt2.rep_mk = cbrt2
```

An element prints as its coordinates, a rational polynomial in the generator:

```lean (name := cbrt2Pow)
#eval c ^ 5
```
```leanOutput cbrt2Pow
2*x^2
```

```lean -show
end HexNumberFieldChapter
```

The last check converts the coordinate form back to a canonical number and
recovers the number it came from.

{docstring Hex.QAdjoin}

# Performance
%%%
tag := "hex-number-field-performance"
%%%

Fixed-field arithmetic is polynomial arithmetic and scales as the degree
suggests: multiplication is quadratic in the degree and inversion cubic with a
logarithmic factor for coefficient growth. Everything that isolates roots is
dominated by the isolation, so those rows are fixed inputs rather than
asymptotics.

:::table +header
* * operation
  * input
  * time
* * `QAdjoin` multiplication
  * degree 16, dense coordinates
  * 0.12 ms
* * `QAdjoin` inversion
  * degree 16, dense coordinates
  * 0.71 ms
* * `QAdjoin.approx`
  * degree 128, fixed precision
  * 17 ms
* * `ZPoly.algebraicRoots`
  * `X⁴ − 10X² + 1`, four roots
  * 44 ms
* * `AlgebraicRoot.exact`
  * a root of `∏ (X² − p)`, `p ≤ 13`, degree 12
  * 1.9 ms
* * `AlgebraicRoot.exact`
  * a root of `X⁸ − 2` inside `(X⁸ − 2)(X + 3)`
  * 310 ms
* * `AlgebraicRoot.add`
  * a root of `X⁶ − 2` plus `√3`, degree product 12
  * 4.5 s
* * `AlgebraicPoly.roots`
  * dense degree 6, one `√2` coefficient
  * 6.0 s
:::

Medians on chungus2 from the exports recorded in
`reports/hex-number-field-performance.md` in the `hex-dev` repository;
regenerate with `.lake/build/bin/hexnumberfield_bench run
Hex.NumberFieldBench.<target>`. The last three rows spend over ninety percent
of their time in root isolation of the resultant or eliminant, and the
`X⁸ − 2` exactification spends its time re-isolating candidates rather than
factoring; the SPEC's complexity section records the bounds.

# The Mathlib correspondence
%%%
tag := "hex-number-field-correspondence"
%%%

`HexNumberFieldMathlib` interprets every representation in `ℂ`. Two canonical
numbers with the same complex value are equal, the executable operations
compute the complex ones, and the `Field` instance on
{name}`Hex.AlgebraicNumber` is built from those very operations, so a theorem
proved with the instance is a theorem about the code that ran.

```lean
open Hex HexNumberFieldChapter

example (a b : AlgebraicNumber)
    (h : a.toComplex = b.toComplex) : a = b :=
  AlgebraicNumber.toComplex_injective h

example : (sqrt2 + sqrt3).toComplex =
    sqrt2.toComplex + sqrt3.toComplex :=
  AlgebraicNumber.add_toComplex sqrt2 sqrt3

-- The instance's operations are the executable ones.
example (a b : AlgebraicNumber) :
    a * b = AlgebraicNumber.mul a b := rfl
example (a : AlgebraicNumber) :
    a⁻¹ = AlgebraicNumber.inv a := rfl
```

The roots returned by {name}`Hex.ZPoly.algebraicRoots` are exactly the
complex roots of the polynomial, each once, and the reality test is exact:

{docstring Hex.ZPoly.mem_algebraicRoots_iff}

{docstring Hex.AlgebraicNumber.isReal_iff}

{docstring Hex.AlgebraicPoly.contains_roots_iff}

For a checked fixed presentation, the coordinates of {name}`Hex.QAdjoin` are
ring-equivalent to Mathlib's `AdjoinRoot` of the defining polynomial, and
opening the scope `Hex.QAdjoin.QAdjoinField` gives them Mathlib's field
notation and laws, noncomputably; executable code keeps the unscoped
operations.

# Cross-references
%%%
tag := "hex-number-field-cross-references"
%%%

* {ref "hex-poly-z"}[HexPolyZ] provides integer polynomials, the `#p[…]`
  literal, and squarefree parts.
* {ref "hex-roots"}[HexRoots] isolates complex roots and certifies the discs
  every algebraic number carries.
* {ref "hex-resultant"}[HexResultant] computes the resultants behind lazy
  addition and multiplication.
* {ref "factor-tactics"}[Factor tactics] describes the integer factorization
  behind `exact`.
* {ref "hex-real-roots"}[HexRealRoots] isolates real roots with a statement
  of how many there are; `isReal` here only tests one root.
* {ref "hex-number-field-tower"}[HexNumberFieldTower] works with several
  generators at once and flattens them to one.
