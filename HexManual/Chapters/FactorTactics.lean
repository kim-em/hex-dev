/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexBerlekampMathlib
import HexBerlekampZassenhausMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "`factor_poly` and `irreducibility`: certified factoring" =>
%%%
tag := "factor-tactics"
%%%

# Introduction
%%%
tag := "factor-tactics-intro"
%%%

`factor_poly` produces a certified factorization of a concrete
polynomial. `irreducibility` proves that a concrete polynomial is
irreducible. Both commands run compiled search during elaboration and
emit a proof term containing only reified data and verified certificate
checks.

The supported input types depend on the imported library:

* `HexBerlekamp` supports {name}`Hex.FpPoly`;
* `HexBerlekampMathlib` adds `Polynomial (ZMod p)`;
* `HexBerlekampZassenhaus` adds {name}`Hex.ZPoly`;
* `HexBerlekampZassenhausMathlib` adds `Polynomial ℤ`.

# Proving irreducibility
%%%
tag := "factor-tactics-irreducibility"
%%%

The bare tactic closes an `Irreducible` goal:

```lean
open Polynomial

example : Irreducible (X ^ 2 - 2 : Polynomial ℤ) := by
  irreducibility
```

It can also be used as a term:

```lean
open Polynomial

theorem sqrt2_irred :
    Irreducible (X ^ 2 - 2 : Polynomial ℤ) :=
  irreducibility (X ^ 2 - 2 : Polynomial ℤ)
```

With an explicit polynomial in tactic mode, the unnamed form adds a
hypothesis called `this`, while the named form chooses a name:

```lean
open Polynomial

example :
    Irreducible (X ^ 2 - 2 : Polynomial ℤ) ∧
      Irreducible (X ^ 2 + X + 1 : Polynomial ℤ) := by
  irreducibility (X ^ 2 - 2 : Polynomial ℤ)
  irreducibility h : (X ^ 2 + X + 1 : Polynomial ℤ)
  exact ⟨this, h⟩
```

The same syntax proves the Mathlib-free predicate on dense integer
polynomials:

```lean
open Hex

def quadZ : ZPoly := #p[1, 0, 1]

theorem quadZ_irred : ZPoly.Irreducible quadZ :=
  irreducibility quadZ
```

The correspondence library proves that {name}`Hex.ZPoly.Irreducible`
agrees with Mathlib's `Irreducible` predicate after conversion to
`Polynomial ℤ`.

# Producing a factorization
%%%
tag := "factor-tactics-factor-poly"
%%%

For a `Polynomial ℤ` input, `factor_poly` returns
{name}`Hex.FactoredPoly`: a scalar, a list of irreducible factors, and
proofs that the scalar times their product is the input.

```lean
open Polynomial

noncomputable def facZ :=
  factor_poly ((X - 1) ^ 2 * (X ^ 2 + 1) * 6 : Polynomial ℤ)

example : facZ.scalar = 6 := rfl
example : facZ.factors.length = 3 := rfl
```

The tactic form introduces transparent local names and their proofs:

```lean
open Polynomial

example : True := by
  factor_poly ((X - 1) * (X + 1) : Polynomial ℤ)
  have _ := factors_mul
  have _ := factors_irred
  trivial
```

Over a prime field, the result has the analogous
{name}`Hex.FpPoly.Factored` type:

```lean
open Hex

def fp : FpPoly 5 := #p[4, 0, 1]

def fpFactors : FpPoly.Factored fp :=
  factor_poly fp
```

# Certificates and trust
%%%
tag := "factor-tactics-trust"
%%%

Parsing produces an executable dense polynomial together with a proof
that it denotes the user's expression. Compiled search then finds
factors and irreducibility witnesses. The emitted term checks:

* coefficient-level reconstruction of the input;
* one irreducibility certificate for each distinct factor;
* the conversion equality between dense and Mathlib polynomials, when
  the input uses a Mathlib type.

Finite-field factors use Rabin certificates. Integer factors first try
small-prime irreducibility and multi-prime degree obstructions. The
factorization and certificate generators are not trusted: only the
small checkers and their Lean proofs are part of the logical argument.

The ordinary tactics accept closed expressions built from variables,
constants, numerals, addition, subtraction, multiplication, negation,
and natural powers. Named definitions may be unfolded within a fixed
fuel limit. Unsupported syntax or an unavailable certificate produces
an elaboration error rather than an unproved term.

# Kernel-evaluated fallbacks
%%%
tag := "factor-tactics-kernel"
%%%

`irreducibility!` and `factor_poly!` first try the ordinary
certificate forms. If no compact certificate is available, they may
ask the kernel to evaluate the decidable irreducibility procedure.
This can handle balanced examples outside the certificate languages,
but it is intentionally restricted to small dense polynomials because
kernel evaluation is much slower than compiled search.

The fallback also requires the complete executable definitions to be
visible in the calling module. It cannot evaluate the native LLL
function used by lattice recombination. For routine proofs, the plain
forms are preferable: they provide smaller proof terms, clearer
failure messages, and predictable checking cost.

# Mathematical algorithms

The tactics are only the proof-producing user interface. The
underlying algorithms are described separately:

* {ref "hex-berlekamp"}[finite-field Berlekamp factorization] explains
  Frobenius fixed spaces and Rabin certificates;
* {ref "hex-berlekamp-zassenhaus"}[integer
  Berlekamp-Zassenhaus factorization] explains normalization, Hensel
  lifting, subset recombination, and logarithmic-derivative lattice
  recombination;
* {ref "hex-hensel"}[HexHensel] gives the lifting constructions;
* {ref "hex-lll"}[HexLLL] gives the certified lattice reduction used
  during lattice recombination.
