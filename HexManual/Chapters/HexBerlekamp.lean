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

local instance boundsFive : ZMod64.Bounds 5 :=
  ⟨by decide, by decide⟩

def f : FpPoly 5 := #p[1, 0, 1]

#check Berlekamp.berlekampFactor
#check Berlekamp.rabinTest
```

The ordinary umbrella contains the executable factorization and the
certificate-backed `factor_poly` and `irreducibility` syntax for
`FpPoly p`. Importing `HexBerlekampMathlib` adds the corresponding
surface for `Polynomial (ZMod p)`.

# The Mathlib correspondence
%%%
tag := "hex-berlekamp-mathlib"
%%%

Everything above is executable and Mathlib-free. `HexBerlekampMathlib`
is the companion that transports it: `toMathlibPolynomial` maps a
{name}`Hex.FpPoly` to `Polynomial (ZMod p)`, and the executable checks
become statements about Mathlib's `Irreducible` predicate on the
transported polynomial.

The headline equivalence takes an arbitrary input. The computable test
{name}`HexBerlekampMathlib.fpIsIrreducible` normalizes to a monic
polynomial, runs Rabin's test on it, and agrees exactly with Mathlib
irreducibility:

{docstring HexBerlekampMathlib.fpIsIrreducible_iff}

For a monic input the equivalence is Rabin's criterion itself, in both
directions: the test succeeds exactly on the irreducible polynomials.
The forward direction is what certificate checking uses; the reverse
direction says the test never misses.

{docstring HexBerlekampMathlib.rabin_irreducible}

Factorization transports factor by factor. On a monic square-free input
of positive degree, every entry of the list returned by
{name}`Hex.Berlekamp.berlekampFactor` is irreducible in Mathlib's sense.
Together with the Mathlib-free product theorem
{name}`Hex.Berlekamp.prod_berlekampFactor` above, the returned list is a
complete factorization into Mathlib irreducibles.

{docstring HexBerlekampMathlib.irreducible_of_mem_berlekampFactor}

The proof boundary follows the import boundary. The executable library
proves what is statable without Mathlib: the product identity, degree
accounting, and the loop invariants of the factor loop. The companion
supplies the finite-field theory, such as the existence and subfield
structure of `𝔽_(p^n)` behind Rabin's criterion, that reads those checks
as irreducibility.

# Verification

The executable library proves product reconstruction and the algebra
of the Berlekamp and Rabin checks. The Mathlib companion proves that
successful certificates imply the usual `Irreducible` predicate and
that the factors returned from a square-free input are irreducible.
Certificate generation is search; the small checker and its proof
determine what is trusted.
