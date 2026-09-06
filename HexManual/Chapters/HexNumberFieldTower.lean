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

`HexNumberFieldTower` builds number fields one generator at a time: `ℚ`, then
`ℚ(α₁)`, then `ℚ(α₁, α₂)`, each step adjoining a root of a polynomial that is
irreducible over the field so far. Elements are stored as rational coordinates
in the product basis of the tower, and arithmetic is polynomial arithmetic
modulo the defining polynomials. Every tower also comes with a fixed embedding
into `ℂ`, so a tower is a particular subfield of `ℂ` rather than a field known
up to isomorphism. The embedding is what lets the library answer questions an
abstract presentation cannot: which root of `X² − 2` the generator denotes, and
therefore whether a given algebraic number already lies in the field.

Four operations do the work. {name}`Hex.NumberTower.factor?` factors a
polynomial over a tower by Trager's method, one level at a time.
{name}`Hex.NumberTower.adjoin?` adjoins a specified algebraic number and
recognises when it is already present. {name}`Hex.NumberTower.split?`
alternates factoring and adjoining until a polynomial splits into linear
factors, and returns the splitting field together with all of the roots.
{name}`Hex.NumberTower.flatten?` replaces a tower by a single primitive element
with exact coordinate changes in both directions, so a computation can move
between the tower and the one-generator form {name}`Hex.QAdjoin` of
`HexNumberField`.

Each operation checks its own result before returning it, and returns `none`
otherwise. The correspondence library `HexNumberFieldTowerMathlib` proves that
`none` never occurs, that arithmetic in a tower computes the corresponding
complex arithmetic, and it states what each result means: the factors are
irreducible and multiply back to the input, the adjoined generator has the
requested complex value, and the splitting field contains every root.

{docstring Hex.NumberTower.Extension}

# ℚ(√2)
%%%
tag := "hex-number-field-tower-adjoin"
%%%

Every tower starts from {name}`Hex.NumberTower.rat`, the tower with no
extensions, whose elements are the rational numbers. Adjoining an algebraic
number to it with {name}`Hex.NumberTower.adjoin?` returns an extension that
carries the new tower, its generator `gen`, and the inclusion `embed` of the
field below. Coordinates in `ℚ(√2)` are the pair `#[a, b]` standing for
`a + b√2`:

```lean
open Hex Hex.NumberTower

namespace HexNumberFieldTowerChapter

def sqrt2 : AlgebraicNumber :=
  (ZPoly.algebraicRoots #p[-2, 0, 1])[1]!
def sqrt3 : AlgebraicNumber :=
  (ZPoly.algebraicRoots #p[-3, 0, 1])[1]!

-- `adjoin` is the companion's total form of `adjoin?`, which
-- never returns `none` (`adjoin?_isSome`).
def Q2 : Extension NumberTower.rat :=
  adjoin NumberTower.rat sqrt2.toRoot
abbrev T2 : NumberTower := Q2.tower
def r2 : Elem T2 := Q2.gen

#guard T2.dim = 2
#guard coeffs (r2 * r2) = #[2, 0]
#guard coeffs (Q2.embed (ofRat NumberTower.rat 5)) = #[5, 0]

-- √2 is already there: adjoining it again changes nothing.
#guard (adjoin T2 sqrt2.toRoot).tower.dim = 2
```

{docstring Hex.NumberTower.adjoin?}

# Factoring over ℚ(√2)
%%%
tag := "hex-number-field-tower-factor"
%%%

`X⁴ − 10X² + 1` is irreducible over `ℚ`: it is the minimal polynomial of
`√2 + √3`. Over `ℚ(√2)` it splits into two quadratics, because
`(X² − 1)² − 8X² = X⁴ − 10X² + 1` and `8 = (2√2)²`. The tower's factorization
finds exactly those two factors, with the scalar `1` kept separate:

```lean
def quartic : Poly T2 :=
  liftZPoly T2 #p[1, 0, -10, 0, 1]
def gPlus : Poly T2 := #p[-1, (2 : Rat) • r2, 1]
def gMinus : Poly T2 := #p[-1, (-2 : Rat) • r2, 1]

#guard gPlus * gMinus = quartic

#guard
  let F := factor T2 quartic
  coeffs F.scalar = #[1, 0] &&
    F.factors.all (fun g => g.2 = 1) &&
    F.factors.map (·.1) == #[gMinus, gPlus]
```

At each level `K(α)/K` the method searches a fixed list of integer shifts for
a squarefree relative norm, factors that norm over `K`, and recovers the
factors over `K(α)` by gcd; the base case over `ℚ` is the
{ref "factor-tactics"}[integer factorizer].

{docstring Hex.NumberTower.factor?}

# Splitting and flattening
%%%
tag := "hex-number-field-tower-split"
%%%

`(X² − 2)(X² − 3)` needs two genuine extensions to split. The splitting field
has dimension four and the four roots square to `2` or `3`:

```lean
def biquadratic : Poly NumberTower.rat :=
  liftZPoly NumberTower.rat #p[6, 0, -5, 0, 1]

/-- The finite root list; empty for the zero polynomial. -/
def finiteRoots {T : NumberTower} :
    Roots T → Array (Elem T × Nat)
  | .finite rs => rs
  | .all => #[]

#guard
  let S := split NumberTower.rat biquadratic
  S.extension.tower.dim = 4 &&
    let rs := finiteRoots S.roots
    rs.size = 4 && rs.all fun r =>
      r.2 = 1 &&
        (coeffs (r.1 * r.1) = #[2, 0, 0, 0] ||
          coeffs (r.1 * r.1) = #[3, 0, 0, 0])
```

Building the same field by hand, `ℚ(√2)(√3)`, and flattening it recovers the
classical primitive element: `√2 + √3` generates the field, its minimal
polynomial is the quartic above, and `√2 = (γ³ − 9γ)/2` in terms of the
generator `γ`:

```lean
def Q23 : Extension T2 := adjoin T2 sqrt3.toRoot
abbrev T23 : NumberTower := Q23.tower
def s2 : Elem T23 := Q23.embed r2
def s3 : Elem T23 := Q23.gen

#guard T23.dim = 4
#guard (s2 + s3) * (s2 - s3) = ofRat T23 (-1)

#guard
  let F := flatten T23
  F.root.p = #p[1, 0, -10, 0, 1] &&
    (F.toPrimitive s2).coeffs = #p[0, -9 / 2, 0, 1 / 2] &&
    (F.toPrimitive s3).coeffs = #p[0, 11 / 2, 0, -1 / 2] &&
    F.fromPrimitive (F.toPrimitive s3) == s3

end HexNumberFieldTowerChapter
```

{docstring Hex.NumberTower.split?}

{docstring Hex.NumberTower.flatten?}

The `Option`-valued operations are the computational library's; the total
forms {name}`Hex.NumberTower.adjoin`, {name}`Hex.NumberTower.factor`,
{name}`Hex.NumberTower.split` and {name}`Hex.NumberTower.flatten` come from
the Mathlib companion, which unwraps each option with its completeness
theorem.

# Performance
%%%
tag := "hex-number-field-tower-performance"
%%%

Coordinate arithmetic scales with the dimension `D` of the tower: addition is
linear, multiplication quadratic, and inversion runs an extended gcd over the
field below. The composite operations mix factoring, root isolation and
adjoining, whose relative weights change with the degree, so they are recorded
on fixed inputs rather than as asymptotics.

:::table +header
* * operation
  * input
  * time
* * `adjoin?`
  * `2^{1/4}` to `ℚ(√2)`
  * 311 ms
* * `adjoin?`
  * `√2` to `ℚ(√2)`, already present
  * 18 ms
* * `factor?`
  * `X² − X − 1` over `ℚ(√2, √3)`
  * 7.9 ms
* * `factor?`
  * `X²⁴ − X − 1` over `ℚ(√2)`
  * 250 ms
* * `split?`
  * `(X² − 2)(X² − 3)` over `ℚ`
  * 68 ms
* * `flatten?`
  * `ℚ(√2, √3)`
  * 21 ms
* * inversion
  * dimension 24, `ℚ(3^{1/12}, √2)`
  * 7.0 ms
:::

Per-call medians on chungus2 from the exports recorded in
`reports/hex-number-field-tower-performance.md` in the `hex-dev` repository;
regenerate with `.lake/build/bin/hexnumberfieldtower_bench run
Hex.NumberTowerBench.<target>`. Factoring over a number field is far slower
than PARI's `nffactor` on the same inputs (fifty to three hundred times on
the Selmer family `Xⁿ − X − 1` over `ℚ(√2)`); the report records the
comparison and its provenance.

# The Mathlib correspondence
%%%
tag := "hex-number-field-tower-correspondence"
%%%

`HexNumberFieldTowerMathlib` interprets every element of a validated tower in
`ℂ` through the stored embedding. That interpretation is injective and
respects the executable arithmetic, and each of the four operations has a
soundness theorem describing its result and a completeness theorem stating
that it never returns `none` on a valid tower.

```lean
open Hex Hex.NumberTower HexNumberFieldTowerChapter

example (a b : Elem T23) :
    T23.toComplex (a * b) =
      T23.toComplex a * T23.toComplex b :=
  map_mul T23 a b

example (a b : Elem T23)
    (h : T23.toComplex a = T23.toComplex b) : a = b :=
  toComplex_injective T23 h
```

{docstring Hex.NumberTower.adjoin?_sound}

{docstring Hex.NumberTower.flatten?_sound}

# Cross-references
%%%
tag := "hex-number-field-tower-cross-references"
%%%

* {ref "hex-number-field"}[HexNumberField] supplies the algebraic numbers
  that are adjoined, and the one-generator form that flattening targets.
* {ref "hex-resultant"}[HexResultant] computes the norms in Trager's method.
* {ref "factor-tactics"}[Factor tactics] describes the integer factorization
  at the bottom of every tower.
