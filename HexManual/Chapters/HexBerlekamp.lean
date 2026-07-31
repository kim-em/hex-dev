/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexBerlekampMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexBerlekamp: factorization over finite fields" =>
%%%
tag := "hex-berlekamp"
%%%

# The problem

`HexBerlekamp` factors dense polynomials over the prime field
`𝔽_p`. Its principal executable type is {name}`Hex.FpPoly`.
The library also supplies Rabin's irreducibility test and a
distinct-degree factorization.

For a monic square-free polynomial `f` of degree `n`, Berlekamp's
method studies the Frobenius map `h ↦ h^p mod f` on the
`n`-dimensional vector space `𝔽_p[X] / (f)`. In the basis
`1, X, ..., X^(n-1)`, subtracting the identity gives the
Berlekamp matrix `Q_f - I`.

# Fixed points and factors

The kernel of `Q_f - I` consists of residue classes satisfying
`h^p = h`. If `f = f₁ ··· fᵣ` is a product of distinct monic
irreducibles, the Chinese remainder
theorem identifies that kernel with `𝔽_p^r`: a fixed residue is
constant on each irreducible factor. Its dimension is therefore the
number of irreducible factors.

This gives both a test and a factorization procedure:

* `f` is irreducible exactly when the kernel contains only constants;
* a nonconstant kernel element `h` splits a current factor by the
  greatest common divisors `gcd(f, h - c)` for `c ∈ 𝔽_p`;
* repeating these splits over a kernel basis produces the complete
  factorization.

The executable construction uses exact row reduction over `𝔽_p`.
The product theorem is proved without Mathlib:

{docstring Hex.Berlekamp.prod_berlekampFactor}

`HexBerlekampMathlib` transfers the result through the ring
equivalence with `Polynomial (ZMod p)` and proves irreducibility of
the returned factors.

# Rabin's irreducibility test

Rabin's criterion avoids constructing a complete factorization. A
monic polynomial `f` of degree `n` over `𝔽_p` is irreducible exactly
when `f ∣ X^(p^n) - X` and, for every prime divisor `q` of `n`,
`gcd(f, X^(p^(n/q)) - X) = 1`.

The first condition says that all roots of `f` lie in `𝔽_(p^n)`.
The remaining conditions rule out roots in every proper maximal
subfield. Hex checks the criterion by modular exponentiation and
greatest-common-divisor computations and records the intermediate
data in an irreducibility certificate.

# Using the executable API

```lean
open Hex

def f : FpPoly 5 := #p[1, 0, 1]

#check Berlekamp.berlekampFactor
#check Berlekamp.rabinTest
```

The ordinary umbrella contains the executable factorization and the
certificate-backed `factor_poly` and `irreducibility` syntax for
`FpPoly p`. Importing `HexBerlekampMathlib` adds the corresponding
surface for `Polynomial (ZMod p)`.

# Verification

The executable library proves product reconstruction and the algebra
of the Berlekamp and Rabin checks. The Mathlib companion proves that
successful certificates imply the usual `Irreducible` predicate and
that the factors returned from a square-free input are irreducible.
Certificate generation is search; the small checker and its proof
determine what is trusted.
