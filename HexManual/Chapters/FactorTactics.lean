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

local instance boundsFive : ZMod64.Bounds 5 := ⟨by decide, by decide⟩

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

The generated proofs use only Lean and Mathlib's documented
foundations:

```lean (name := axiomsCheck)
#print axioms sqrt2_irred
```
```leanOutput axiomsCheck
'sqrt2_irred' depends on axioms: [propext, Classical.choice, Quot.sound]
```

# Coverage and failure messages
%%%
tag := "factor-tactics-coverage"
%%%

Every input must be a closed term. A polynomial mentioning a local
hypothesis or metavariable is rejected. Executable `FpPoly` and
`ZPoly` inputs must also be definitionally transparent, so compiled
evaluation and kernel checking can both see their coefficients.

Mathlib `Polynomial` inputs are parsed from `X`, `Polynomial.C`,
numerals, addition, subtraction, multiplication, negation, and powers
with literal natural exponents. Named definitions are unfolded within
a fixed fuel limit. Other constructors, such as a raw
`Polynomial.monomial` application, receive an unsupported-syntax
error even when the term is closed.

For `FpPoly p`, every closed input at a literal prime modulus inside
the `ZMod64` bounds is covered, subject to the Rabin-certificate replay
budget

`(degree + 1) · p ≤ 2²⁶`.

The budget is checked once for each distinct factor. An over-budget
input is rejected during elaboration instead of emitting a proof that
would be too expensive to check. A composite modulus is rejected with
a message saying that the modulus is not prime.

Integer factor search is total, but the plain tactics still need a
small certificate for each irreducible factor. They recognize:

* prime constants and primitive linear polynomials;
* irreducibility after reduction at a prime below `512`;
* Eisenstein's criterion after shifts `0, ±1, ±2, ±3`, with witness
  primes at most `128`;
* multi-prime degree obstructions using primes from `3` through `71`.

These bounded searches do not cover every irreducible polynomial.
Balanced Swinnerton-Dyer examples can be reducible at every candidate
prime, fail all of the small Eisenstein shifts, and retain a possible
proper factor degree in every modular factorization. The plain tactics
then report the factor they could not certify and point to the
kernel-evaluated forms. They never weaken the requested statement.

Zero polynomials and units receive targeted messages rather than false
irreducibility proofs. A reducible input to `irreducibility` reports
the factor count found by `factor_poly`.

# Kernel-evaluated fallbacks
%%%
tag := "factor-tactics-kernel"
%%%

`irreducibility!` and `factor_poly!` first try the ordinary
certificate forms. If no compact certificate is available, they may
ask the kernel to evaluate the decidable irreducibility procedure.
This can handle balanced examples outside the certificate languages,
but a dense-size budget of `13` rejects larger inputs because kernel
evaluation is much slower than compiled search.

The fallback also requires the complete executable definitions to be
visible in the calling module. A caller using Lean's `module` system
must `import all` of that executable closure, as demonstrated by
`HexBerlekampZassenhausMathlib.FactorPolyTests`. The fallback cannot
evaluate the native LLL function used by lattice recombination. For
routine proofs, the plain forms are preferable: they provide smaller
proof terms, clearer failure messages, and predictable checking cost.

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
