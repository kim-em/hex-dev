/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexNumberFieldTowerMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexNumberFieldTower: successive algebraic extensions" =>
%%%
tag := "hex-number-field-tower"
%%%

# Introduction
%%%
tag := "hex-number-field-tower-intro"
%%%

`HexNumberFieldTower` performs exact arithmetic, factorization, adjoining, and
splitting in a sequence of relative algebraic extensions.

# Validated towers and coordinates
%%%
tag := "hex-number-field-tower-data"
%%%

`HexNumberFieldTower` represents a fixed embedding of a successive extension
`ℚ(α₁,…,αₙ)`. Levels are stored newest first; element coordinates use the
mixed-radix order in which the oldest generator varies fastest. Constructors
validate coefficient widths, relative irreducibility, and vanishing at the
chosen absolute root before a level enters a public tower.

{docstring Hex.NumberTower.ofQAdjoin}

The rational base tower is useful on its own and illustrates the coordinate
normalization and total arithmetic conventions:

```lean
open Hex Hex.NumberTower

#guard rat.dim = 1
#guard coeffs (ofRat rat 7 / ofRat rat 3) = #[7 / 3]
#guard coeffs ((0 : Elem rat)⁻¹) = #[0]
```

# Factorization by relative norms
%%%
tag := "hex-number-field-tower-factor"
%%%

{name}`Hex.NumberTower.factor?` performs Yun decomposition and then recursively
applies Trager's algorithm one level at a time. At `K(α)/K`, it searches a
deterministic finite list of integer shifts for a squarefree relative norm,
factors that norm over `K`, and recovers the factors over `K(α)` by gcd. It does
not replace this step with an absolute norm, which would duplicate factors
defined over an intermediate subfield. The rational base case delegates to
the `HexBerlekampZassenhaus` integer factorizer.

{docstring Hex.NumberTower.Norm.oneLevel}

{docstring Hex.NumberTower.factor?}

The returned payload keeps the scalar separate and records each distinct
factor once with a positive multiplicity.

The following example constructs `ℚ(√2)` and factors `X² - 2` there; the
two linear factors correspond to the already-present roots `±√2`.

```lean
open Hex Hex.NumberTower

namespace HexNumberFieldTowerChapter

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
    if hsimple : HasOnlySimpleRoots sqrtTwoPoly then
      let extension := ofQAdjoin (x := sqrtTwoRoot)
        hsimple sqrtTwoRep rfl
      let f : Poly extension.tower :=
        DensePoly.ofCoeffs
          #[ofRat extension.tower (-2), 0, 1]
      match factor? extension.tower f with
      | some result =>
          result.factors.size = 2 &&
            result.factors.all fun entry =>
              entry.1.degree? = some 1 && entry.2 = 1
      | none => false
    else
      false
  else
    false

end HexNumberFieldTowerChapter
```

# Adjoining and splitting
%%%
tag := "hex-number-field-tower-split"
%%%

Adjoining selects the unique relative factor that contains the requested
absolute algebraic root under the tower's fixed embedding. If that factor is
linear, the root was already present and the result is an identity extension.

{docstring Hex.NumberTower.adjoin?}

Splitting alternates factorization and genuine adjoining steps until every
factor is linear. The zero polynomial uses `.all`; a nonzero constant returns
an empty finite root array.

{docstring Hex.NumberTower.split?}

# Flattening to one primitive element
%%%
tag := "hex-number-field-tower-flatten"
%%%

{name}`Hex.NumberTower.flatten?` replaces a tower by one canonical
{name}`Hex.QAdjoin` presentation. It combines the fixed generators in deterministic
signed-shift order, retries both degree and coordinate-recovery collisions,
recovers old generators by exact gcd, and checks direct-evaluation coordinate
maps, a tower-basis round trip, and the primitive polynomial relation before
returning maps.

{docstring Hex.NumberTower.flatten?}

# Companion contracts
%%%
tag := "hex-number-field-tower-correspondence"
%%%

`HexNumberFieldTowerMathlib` interprets mixed-radix coordinates in the stored
complex embedding, states the arithmetic and relative-resultant
correspondence, and characterizes complete factorization, adjoining,
splitting, and flattening.

{docstring Hex.NumberTower.toComplex}

{docstring Hex.NumberTower.factor?_sound}

{docstring Hex.NumberTower.adjoin?_sound}

{docstring Hex.NumberTower.split?_sound}

{docstring Hex.NumberTower.flatten?_sound}

# Cross-references
%%%
tag := "hex-number-field-tower-cross-references"
%%%

* {ref "hex-number-field"}[HexNumberField] supplies selected algebraic roots,
  canonical exactification, and the one-generator target of flattening.
* {ref "hex-resultant"}[HexResultant] supplies one-level relative elimination.
* {ref "factor-tactics"}[Factor tactics] describes the
  `HexBerlekampZassenhaus` integer factorizer used at the rational base case.
