/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexPolyFast

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexPolyFast: fast dense polynomials" =>
%%%
tag := "hex-poly-fast"
%%%

# Introduction
%%%
tag := "hex-poly-fast-intro"
%%%

`HexPolyFast` adds proof-carrying fast algorithms to the normalized dense
polynomials from {ref "hex-poly"}[`HexPoly`]. The underlying multiplication
and Euclidean operations remain the semantic reference. Optimized kernels
are selected explicitly, and their laws state exact equality with that
reference rather than equality only up to normalization or a unit.

The library covers full and clipped Karatsuba multiplication, Newton
reciprocals and division, half-gcd, product and remainder trees, reusable
multipoint evaluation and interpolation, and Padé approximation. It is
Mathlib-free. Its other direct dependency is
{ref "hex-truncated-series"}[`HexTruncatedSeries`], whose fixed-precision
series representation supplies the Newton-inversion boundary.

# Multiplication plans
%%%
tag := "hex-poly-fast-plans"
%%%

{name}`Hex.DensePoly.MulPlan` packages full multiplication, specialized
squaring, and an arbitrary product slice. Its three proof fields identify
all results with the existing `DensePoly` product. A plan is an ordinary
value, not a typeclass instance, so callers can choose a coefficient-specific
kernel locally without changing global arithmetic.

{docstring Hex.DensePoly.schoolbookPlan}

{docstring Hex.DensePoly.karatsubaPlan}

{docstring Hex.DensePoly.mulWith}

{docstring Hex.DensePoly.squareWith}

{docstring Hex.DensePoly.mulLow}

{docstring Hex.DensePoly.mulSlice}

{docstring Hex.DensePoly.mulMiddleChecked}

The following example selects a small Karatsuba cutoff and checks full and
clipped multiplication against the schoolbook semantics.

```lean
open Hex Hex.DensePoly

namespace HexPolyFastChapterMul

private def a : DensePoly Int :=
  #p[3, -2, 0, 5, 1]

private def b : DensePoly Int :=
  #p[-1, 6, 2]

private def plan : MulPlan Int :=
  karatsubaPlan 2

#guard mulWith plan a b = a * b
#guard squareWith plan a = a * a
#guard
  mulSlice plan 2 3 a b =
    schoolbookSlice 2 3 a b
#guard mulSlice plan 30 4 a b = 0

end HexPolyFastChapterMul
```

The projection theorems are the public semantic boundary. Dispatch cutoffs,
recursive splits, and clipped allocation do not appear in their statements.

{docstring Hex.DensePoly.mulWith_eq}

{docstring Hex.DensePoly.squareWith_eq}

{docstring Hex.DensePoly.coeff_mulLow}

{docstring Hex.DensePoly.coeff_mulSlice}

# Cyclic products and series bridges
%%%
tag := "hex-poly-fast-cyclic-series"
%%%

Cyclic and negacyclic products fold a planned ordinary product modulo
`x^n - 1` and `x^n + 1`. The proof-taking forms require positive length;
the checked forms return `none` for length zero.

{docstring Hex.DensePoly.mulCyclic}

{docstring Hex.DensePoly.mulNegacyclic}

{docstring Hex.DensePoly.mulCyclic_eq_modByMonic}

{docstring Hex.DensePoly.mulNegacyclic_eq_modByMonic}

{docstring Hex.DensePoly.mulCyclic?}

{docstring Hex.DensePoly.mulNegacyclic?}

Reversal converts the leading end of a polynomial to the low end of a fixed
series prefix. The guarded coefficient theorem matters because natural-number
subtraction saturates below zero.

{docstring Hex.DensePoly.reverseSeries}

{docstring Hex.DensePoly.coeff_reverseSeries}

{docstring Hex.DensePoly.polyOfSeries}

{docstring Hex.DensePoly.seriesMulUpTo}

{docstring Hex.DensePoly.reciprocalWith}

{docstring Hex.DensePoly.reciprocalWith_eq}

# Newton division
%%%
tag := "hex-poly-fast-division"
%%%

{name}`Hex.DensePoly.DivPlan` caches a divisor and a finite-precision
reciprocal. The capacity records the largest quotient prefix the plan can
serve. Monic construction works over a commutative ring; field construction
uses the inverse of the leading coefficient.

{docstring Hex.DensePoly.DivPlan.ofMonic}

{docstring Hex.DensePoly.DivPlan.ofNonzero}

{docstring Hex.DensePoly.DivPlan.divMod}

{docstring Hex.DensePoly.DivPlan.mod}

The one-shot interfaces preserve all existing conventions, including
division by zero and a divisor larger than the dividend.

{docstring Hex.DensePoly.divModMonicWith}

{docstring Hex.DensePoly.divModWith}

{docstring Hex.DensePoly.divModWith_eq}

```lean
open Hex Hex.DensePoly

namespace HexPolyFastChapterDivision

private def a : DensePoly Rat :=
  #p[3, -2, 0, 5, 1]

private def b : DensePoly Rat :=
  #p[2, -3, 1]

#guard
  divModWith (karatsubaPlan 2) a b =
    divMod a b
#guard
  divModWith (karatsubaPlan 2) a 0 =
    (0, a)
#guard
  divModWith (karatsubaPlan 2) (a * b) b =
    (a, 0)

end HexPolyFastChapterDivision
```

# Half-gcd
%%%
tag := "hex-poly-fast-half-gcd"
%%%

{name}`Hex.DensePoly.GcdStep` is the two-by-two polynomial transformation
used by half-gcd. It keeps this library independent of the matrix hierarchy.
Recursive high-half calls predict and group the existing Euclidean quotient
sequence; a checked fallback preserves exact executable behavior.

{docstring Hex.DensePoly.gcdWith}

{docstring Hex.DensePoly.xgcdWith}

{docstring Hex.DensePoly.xgcdLeftWith}

{docstring Hex.DensePoly.gcdWith_eq}

{docstring Hex.DensePoly.xgcdWith_eq}

{docstring Hex.DensePoly.xgcdLeftWith_eq}

# Product trees and multipoint operations
%%%
tag := "hex-poly-fast-multipoint"
%%%

{name}`Hex.DensePoly.ProductTree` stores a balanced tree of nonempty levels.
Its observations expose the original leaves, the root product, and individual
node products while hiding the internal level representation.

{docstring Hex.DensePoly.ProductTree.build}

{docstring Hex.DensePoly.ProductTree.root}

{docstring Hex.DensePoly.ProductTree.nodeProduct?}

{name}`Hex.DensePoly.EvalPlan` specializes the leaves to `x - a` and caches
the reciprocal plans used by its remainder tree. Evaluation is total: inputs
within capacity use the tree, and oversized inputs use direct pointwise
evaluation.

{docstring Hex.DensePoly.EvalPlan.build}

{docstring Hex.DensePoly.EvalPlan.eval}

{docstring Hex.DensePoly.EvalPlan.get_eval}

{name}`Hex.DensePoly.InterpPlan` additionally requires a field and distinct
points. Plan construction rejects exactly duplicate points, while interpolation
rejects exactly a mismatch between point and value counts.

{docstring Hex.DensePoly.InterpPlan.build?}

{docstring Hex.DensePoly.InterpPlan.interpolate?}

{docstring Hex.DensePoly.InterpPlan.interpolate?_sound}

{docstring Hex.DensePoly.InterpPlan.interpolate?_unique}

```lean
open Hex Hex.DensePoly

namespace HexPolyFastChapterPoints

private def points : Array Rat :=
  #[-1, 0, 2]

private def values : Array Rat :=
  #[6, 3, 3]

private def expected : DensePoly Rat :=
  #p[3, -2, 1]

private def interpolated : Option (DensePoly Rat) :=
  (InterpPlan.build?
    (karatsubaPlan 2) points).bind
      (fun plan => plan.interpolate? values)

#guard interpolated = some expected

#guard
  (InterpPlan.build? (karatsubaPlan 2)
    (#[1, 2, 1] : Array Rat)).isNone

end HexPolyFastChapterPoints
```

# Padé approximation
%%%
tag := "hex-poly-fast-pade"
%%%

{name}`Hex.DensePoly.PadeApproximant` carries a homogeneous numerator and
denominator, their degree bounds, nontriviality, and the required low-order
congruence. {name}`Hex.DensePoly.NormalizedPade` strengthens the denominator's
constant coefficient to one.

{docstring Hex.DensePoly.padeHomogeneous}

{docstring Hex.DensePoly.pade?}

{docstring Hex.DensePoly.pade?_eq_none_iff}

The homogeneous result is total. The normalized operation returns `none`
exactly when no admissible denominator is invertible at the origin.

```lean
open Hex Hex.DensePoly

namespace HexPolyFastChapterPade

private def series : TSeries Rat 3 :=
  TSeries.ofFn fun _ => 1

private def approximant :
    Option (DensePoly Rat × DensePoly Rat) :=
  (pade? (karatsubaPlan 2) series 1 1).map
    (fun approx => (approx.p, approx.q))

#guard approximant = some (C 1, #p[1, -1])

end HexPolyFastChapterPade
```

# Computational boundary and cross-references
%%%
tag := "hex-poly-fast-cross-references"
%%%

All algorithms and correctness theorems in this chapter are Mathlib-free and
run natively in Lean. There is no separate Mathlib companion: the operations
reduce to the existing `DensePoly` semantics, which the
{ref "hex-poly"}[`HexPoly` chapter] and its companion already connect to
Mathlib polynomials.

Coefficient-specific callers construct plans above this dependency boundary.
{ref "hex-poly-z"}[`HexPolyZ`] supplies Kronecker and CRT-NTT integer kernels,
while {ref "hex-poly-fp"}[`HexPolyFp`] supplies direct and auxiliary-prime
NTT multiplication. The generic algorithms here remain their independent
semantic fallback.
