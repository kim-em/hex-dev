/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexPolyZGcd
import HexPolyZGcdMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexPolyZGcd: checked integer-polynomial gcds" =>
%%%
tag := "hex-poly-z-gcd"
%%%

# Introduction
%%%
tag := "hex-poly-z-gcd-intro"
%%%

`HexPolyZGcd` computes greatest common divisors in `ℤ[x]` together with
exact cofactors and replayable coprimality evidence. Its fast routes use
modular images, heuristic reconstruction, and subresultant chains. Every
route passes through the same small checker before its answer becomes public.

The executable library is Mathlib-free. It builds on `HexPolyZ`,
`HexModular`, and `HexResultant`, and it supplies the square-free
decomposition used by integer-polynomial factorization.

# Certificates and exact division
%%%
tag := "hex-poly-z-gcd-certificates"
%%%

{docstring Hex.ZPoly.CoprimeWitness}

{docstring Hex.ZPoly.GcdCert}

{docstring Hex.ZPoly.checkGcd}

{docstring Hex.ZPoly.checkGcd_sound}

The checker verifies two exact product identities, the normalization
convention, coprime cofactor contents, and one modular or integral Bezout
witness. Candidate production is separate from certificate replay.

{docstring Hex.ZPoly.divExact?}

{docstring Hex.ZPoly.divExact?_product}

# Gcd operations
%%%
tag := "hex-poly-z-gcd-operations"
%%%

{docstring Hex.ZPoly.gcdCert}

{docstring Hex.ZPoly.gcd}

{docstring Hex.ZPoly.cofactors}

{docstring Hex.ZPoly.gcdList}

{docstring Hex.ZPoly.lcm}

The usual divisibility laws hold for the checked result, including the
greatestness direction that downstream factorization algorithms need.

{docstring Hex.ZPoly.gcd_dvd_left}

{docstring Hex.ZPoly.gcd_dvd_right}

{docstring Hex.ZPoly.dvd_gcd}

## Worked example
%%%
tag := "hex-poly-z-gcd-worked"
%%%

```lean
open Hex

namespace HexPolyZGcdChapter

def x1 : ZPoly := DensePoly.ofList [1, 1]
def x2 : ZPoly := DensePoly.ofList [2, 1]
def left : ZPoly := x1 * x1 * x2
def right : ZPoly := x1 * x2 * x2

#guard ZPoly.gcd left right == x1 * x2

end HexPolyZGcdChapter
```

# Fast square-free decomposition
%%%
tag := "hex-poly-z-gcd-square-free"
%%%

{docstring Hex.ZPoly.sqfDecomp}

{docstring Hex.ZPoly.sqfDecomp_reassembly_signed}

{docstring Hex.ZPoly.sqfDecomp_squareFreeCore}

The implementation uses the checked integer gcd of a primitive polynomial
and its derivative. Its proof compares the repeated factor with the rational
reference decomposition, then cancels that factor from their signed
reassembly laws.

# The Mathlib correspondence
%%%
tag := "hex-poly-z-gcd-mathlib"
%%%

`HexPolyZGcdMathlib` transports the divisibility and maximality results
through the ring equivalence from `ZPoly` to Mathlib's `Polynomial ℤ`.

{docstring HexPolyZGcdMathlib.gcd_dvd_left}

{docstring HexPolyZGcdMathlib.dvd_gcd}

{docstring HexPolyZGcdMathlib.divExact?_eq_dvd}

The exact-division correspondence records a nonzero-divisor condition.
This distinguishes the executable operation, which rejects division by zero,
from the proposition `0 ∣ 0`, which is true.
