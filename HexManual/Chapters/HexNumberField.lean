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

Approximation refines the stored root representative and evaluates the reduced
coordinate polynomial with dyadic complex-ball Horner arithmetic. The returned
representative can be threaded into the next request so earlier work is not
repeated.

{docstring Hex.QAdjoin.approx}

# Lazy arithmetic and exactification
%%%
tag := "hex-number-field-lazy"
%%%

Every certificate-producing operation has an `Option` form. The total form is
the primary algebraic API; its loud fallback is proved unreachable in
`HexNumberFieldMathlib`.

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

# What the companion proves
%%%
tag := "hex-number-field-correspondence"
%%%

`HexNumberFieldMathlib` interprets every selected root in `ℂ`, proves the fixed
coordinate laws and approximation enclosure, proves exactification and lazy
arithmetic complete, and identifies the root arrays with Mathlib polynomial
roots and multiplicities.

{docstring Hex.AlgebraicRoot.toComplex}

{docstring Hex.QAdjoin.toComplex}

{docstring Hex.AlgebraicRoot.exact_toComplex}

{docstring Hex.AlgebraicPoly.contains_roots_iff}

# Cross-references
%%%
tag := "hex-number-field-cross-references"
%%%

* {ref "hex-roots"}[HexRoots] supplies certified complex-root isolation and
  the root-identity quotient.
* {ref "hex-resultant"}[HexResultant] supplies the eliminants used by lazy
  arithmetic and fixed-field norm candidates.
* {ref "hex-number-field-tower"}[HexNumberFieldTower] builds successive
  extensions when one primitive presentation is not convenient.
