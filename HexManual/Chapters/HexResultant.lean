/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexResultantMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexResultant: subresultants and discriminants" =>
%%%
tag := "hex-resultant"
%%%

# Introduction
%%%
tag := "hex-resultant-intro"
%%%

`HexResultant` computes polynomial resultants and discriminants without
constructing a Sylvester matrix. Its Brown subresultant pseudo-remainder
sequence stays in the coefficient ring and uses exact division only at the
points where the recurrence proves divisibility. This matters for the tower
algorithms later in the manual: their coefficient rings are executable
number-field presentations, not Mathlib fields.

The computational library is Mathlib-free. `HexResultantMathlib` states the
correspondence between the final executable value and
{name}`Polynomial.resultant`, including specialization and discriminant
conventions.

# The executable API
%%%
tag := "hex-resultant-api"
%%%

The public chain records its normalized inputs, every nonzero remainder, and
the terminal principal-subresultant scalar. The scalar is separate because a
defective degree drop can change the exact resultant without changing the last
nonzero polynomial.

{docstring Hex.PRSResult}

{docstring Hex.DensePoly.subresultantChain}

# Certified chain structure
%%%
tag := "hex-resultant-chain-structure"
%%%

The chain representation comes with structural guarantees, not only
executable checks. Every stored term is nonzero; after the two ordered inputs,
each stored polynomial is strictly smaller than its predecessor; and a
nonzero input pair produces at most `min(deg f, deg g) + 2` terms.

{docstring Hex.DensePoly.subresultantChain_ne_zero}

{docstring Hex.DensePoly.subresultantChain_size_strict}

{docstring Hex.DensePoly.subresultantChain_size_le}

## Fuel control

The implementation bounds its recursion with an explicit fuel parameter.
`subresultantOrdered` selects the public `g.size + 1` budget;
`subresultantOrderedFuel` exposes the same recurrence with an explicit budget
for proof auditing. Adding fuel beyond the public budget leaves the result
unchanged.

{docstring Hex.DensePoly.subresultantOrdered}

{docstring Hex.DensePoly.subresultantOrderedFuel}

{docstring Hex.DensePoly.subresultantOrderedFuel_eq}

Most callers need only the scalar resultant:

{docstring Hex.DensePoly.resultant}

The discriminant uses the standard signed derivative-resultant formula, with
the zero and constant conventions handled explicitly:

{docstring Hex.DensePoly.disc}

# A small exact computation
%%%
tag := "hex-resultant-example"
%%%

For `f = X² - 2` and `g = X - 3`, the resultant is `f(3) = 7`; the
discriminant of `f` is `8`. Both checks below run the Mathlib-free algorithm.

```lean
open Hex

namespace HexResultantChapter

private def f : DensePoly Int := DensePoly.ofList [-2, 0, 1]
private def g : DensePoly Int := DensePoly.ofList [-3, 1]

#guard DensePoly.resultant f g = 7
#guard DensePoly.disc f = 8

end HexResultantChapter
```

# Companion contracts
%%%
tag := "hex-resultant-correspondence"
%%%

These declarations describe the executable results in Mathlib terms. The
central contract identifies the executable scalar with Mathlib's
determinant-defined resultant:

{docstring Hex.DensePoly.toPolynomial_resultant}

The specialization contract retains the original formal degrees, so degree
drops after substituting a parameter do not silently change the resultant
convention:

{docstring Hex.DensePoly.eval_resultant}

Independently, Mathlib's resultant has the following proved root-product
formula. It is the algebraic identity the later executable correspondence will
carry into one-level field norms and Trager collision bounds:

{docstring Hex.DensePoly.resultant_eq_leadingCoeff_mul_prod_roots}

# Cross-references
%%%
tag := "hex-resultant-cross-references"
%%%

* {ref "hex-poly"}[HexPoly] supplies the normalized dense representation and
  pseudo-division primitives.
* {ref "hex-number-field"}[HexNumberField] uses bivariate specialization
  vanishing to justify factorization-lazy arithmetic.
* {ref "hex-number-field-tower"}[HexNumberFieldTower] uses the full value and
  root-product correspondence for relative norms and Trager recovery.
