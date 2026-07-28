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

`HexNumberField` provides executable exact arithmetic for selected complex
algebraic roots, both in a fixed rational presentation and in a canonical
minimal-polynomial form.

# Three representations
%%%
tag := "hex-number-field-representations"
%%%

`HexNumberField` provides three complementary exact representations.
{name}`Hex.QAdjoin` stores rational power-basis coordinates in one fixed
irreducible presentation. {name}`Hex.AlgebraicRoot` stores a certified selected
root of a squarefree integer polynomial without requiring that polynomial to
be minimal. {name}`Hex.AlgebraicNumber` is the canonical form: a selected root
of its normalized irreducible minimal polynomial.

The distinction makes routine arithmetic cheaper. Addition and multiplication
first build a resultant eliminant and isolate the intended result; factoring
to a minimal polynomial is postponed until a caller requests
{name}`Hex.AlgebraicRoot.exact`.

# Fixed-field arithmetic and approximation
%%%
tag := "hex-number-field-fixed"
%%%

Fixed-presentation coordinates are always reduced modulo the defining integer
polynomial. Inversion uses polynomial extended gcd and follows the total field
convention `0⁻¹ = 0`.

{docstring Hex.QAdjoin.reduce}

{docstring Hex.QAdjoin.inv}

Approximation takes a root representative, refines it, and evaluates the
reduced coordinate polynomial with dyadic complex-ball Horner arithmetic. The
returned representative can be threaded into the next request so earlier work
is not repeated.

{docstring Hex.QAdjoin.approx}

Here is fixed-field multiplication and inversion in `ℚ(√2)`:

```lean
open Hex

namespace HexNumberFieldChapter

private def sqrtTwoPoly : ZPoly :=
  DensePoly.ofList [-2, 0, 1]

private def sqrtTwoSquare : DyadicSquare :=
  ⟨Dyadic.ofIntWithPrec 181 7, 0, 8⟩

private def sqrtTwoRep : RefinedIsolation sqrtTwoPoly :=
  ⟨⟨sqrtTwoSquare, by decide⟩, by decide⟩

private def sqrtTwoRoot : SimpleRoot sqrtTwoPoly :=
  SimpleRoot.mk sqrtTwoRep

#guard
  if hirred : ZPoly.isIrreducible sqrtTwoPoly = true then
    letI : ZPoly.CheckedIrreducible sqrtTwoPoly :=
      ⟨hirred, by decide⟩
    let xPoly :=
      DensePoly.ofList ([0, 1] : List Rat)
    let x : QAdjoin sqrtTwoPoly sqrtTwoRoot :=
      QAdjoin.reduce sqrtTwoPoly sqrtTwoRoot xPoly
    let two : QAdjoin sqrtTwoPoly sqrtTwoRoot :=
      QAdjoin.reduce sqrtTwoPoly sqrtTwoRoot
        (DensePoly.C 2)
    x * x = two && x * x⁻¹ = 1
  else
    false

end HexNumberFieldChapter
```

# Lazy arithmetic and exactification
%%%
tag := "hex-number-field-lazy"
%%%

Every certificate-producing operation has an `Option` form. The total form is
the primary algebraic API; its loud fallback is paired with a companion
completeness contract.

{docstring Hex.AlgebraicRoot.add?}

{docstring Hex.AlgebraicRoot.mul?}

{docstring Hex.AlgebraicRoot.inv?}

{docstring Hex.AlgebraicRoot.exact?}

{docstring Hex.AlgebraicRoot.exact}

Canonical algebraic numbers reuse these lazy operations and exactify the
answer. Their Boolean equality compares represented values rather than record
layout. Lazy roots deliberately have no `BEq`; the root driver uses checked
{name}`Hex.QAdjoin.Roots.sameValue?` instead.

# Polynomials and roots
%%%
tag := "hex-number-field-roots"
%%%

An {name}`Hex.AlgebraicPoly` owns semantic trailing-zero normalization. This is
separate from `DensePoly AlgebraicNumber`, whose normalizer would require a
structural equality decision that is not the intended algebraic equality.

{docstring Hex.AlgebraicPoly.ofArray}

```lean
open Hex

-- Trailing canonical zeros are removed semantically.
#guard
  let f := AlgebraicPoly.ofArray
    #[AlgebraicNumber.zero, AlgebraicNumber.zero]
  f.isZero && f.coeffs.isEmpty
```

Root APIs distinguish the zero polynomial, whose root set is universal, from a
finite root array carrying positive multiplicities.

{docstring Hex.QAdjoin.roots?}

{docstring Hex.AlgebraicPoly.roots?}

# Companion contracts
%%%
tag := "hex-number-field-correspondence"
%%%

`HexNumberFieldMathlib` interprets selected roots in `ℂ`. For a checked fixed
presentation, the reduced coordinates are now ring-equivalent to the monic
rational `AdjoinRoot` quotient, their executable extended-GCD inverse is
validated, and an opt-in `Field` instance preserves the existing computational
operations and rational scalar action. Open the
`Hex.QAdjoin.QAdjoinField` scope when Mathlib field notation and laws are
wanted.

The later approximation, exactification, lazy-arithmetic, and root-array
contracts remain staged declarations for subsequent proof-completion
milestones.

{docstring Hex.AlgebraicRoot.toComplex}

{docstring Hex.QAdjoin.toComplex}

{docstring Hex.QAdjoin.adjoinRootEquiv}

{docstring Hex.QAdjoin.embedding}

{docstring Hex.AlgebraicRoot.exact_toComplex}

{docstring Hex.AlgebraicPoly.contains_roots_iff}

# Cross-references
%%%
tag := "hex-number-field-cross-references"
%%%

* {ref "hex-poly-z"}[HexPolyZ] supplies the integer-polynomial presentation.
* {ref "hex-roots"}[HexRoots] supplies certified complex-root isolation and
  {name}`Hex.SimpleRoot`.
* {ref "hex-resultant"}[HexResultant] supplies the eliminants used by lazy
  arithmetic and fixed-field norm candidates.
* {ref "hex-matrix"}[HexMatrix] and {ref "hex-row-reduce"}[HexRowReduce]
  supply exact span coordinates for fixed-field minimal polynomials.
* {ref "hex-number-field-tower"}[HexNumberFieldTower] builds successive
  extensions when one primitive presentation is not convenient.
