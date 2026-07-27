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
defined over an intermediate subfield.

{docstring Hex.NumberTower.Norm.oneLevel}

{docstring Hex.NumberTower.factor?}

The returned payload keeps the scalar separate and records each distinct
factor once with a positive multiplicity.

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
`QAdjoin` presentation. It combines the fixed generators in deterministic
signed-shift order, retries both degree and coordinate-recovery collisions,
recovers old generators by exact gcd and row reduction, and checks a tower
basis round trip plus the primitive polynomial relation before returning maps.

{docstring Hex.NumberTower.flatten?}

# What the companion proves
%%%
tag := "hex-number-field-tower-correspondence"
%%%

`HexNumberFieldTowerMathlib` interprets mixed-radix coordinates in the stored
complex embedding. It proves arithmetic correspondence, relative-resultant
agreement, factorization and adjoining completeness, splitting reconstruction
and generation, and both flattening round trips.

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
* {ref "hex-row-reduce"}[HexRowReduce] supplies exact coordinate recovery for
  primitive elements.
