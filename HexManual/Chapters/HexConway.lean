/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexConway

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexConway: Tier 1 Conway-polynomial lookup" =>
%%%
tag := "hex-conway"
%%%

# Introduction
%%%
tag := "hex-conway-intro"
%%%

A *Conway polynomial* `C(p, n)` is the canonical irreducible degree-`n`
polynomial over the prime field `𝔽_p` used to give a standard,
compatible presentation of the finite field `𝔽_{pⁿ}`. The full treatment
of Conway polynomials has three tiers: a Tier 1 lookup of committed
table entries, Tier 2 proofs that those entries satisfy the Conway
compatibility conditions across the subfield lattice, and Tier 3
search for entries beyond the committed table. `HexConway` is the
executable Tier 1 library: it exposes the imported
[Lübeck](http://www.math.rwth-aachen.de/~Frank.Luebeck/data/ConwayPol/)
Conway table as a lookup, keeping the baseline lookup separate from the
later compatibility and search work.

`HexConway` is Mathlib-free. It depends only on `HexBerlekamp` (for the
Rabin irreducibility checker that certifies each committed entry) and
the prime-field polynomial library it reaches through it. Each supported
`(p, n)` pair commits a named polynomial literal, a machine-checked
irreducibility proof, and a {name}`Hex.Conway.SupportedEntry` witness
packaging the lookup together with its proof. See
{ref "hex-conway-cross-references"}[Cross-references].

# The lookup
%%%
tag := "hex-conway-lookup"
%%%

The committed data is a raw coefficient table, stored ascending by
degree and keyed on the pair `(p, n)`. It returns `none` on any pair
outside the committed table.

{docstring Hex.Conway.luebeckConwayCoeffs?}

A small builder turns a list of natural-number coefficients into an
`FpPoly p` by reducing each coefficient into `ZMod64 p` and routing
through the normalizing constructor.

{docstring Hex.Conway.luebeckConwayPolynomialOfCoeffs}

The main entry point composes the two: it looks up the coefficient
list and, on a hit, builds the polynomial. The supported coverage is
`p ∈ {2, 3, 5, 7, 11, 13}` and `n ∈ {1, …, 6}`. Every other pair
returns `none` rather than triggering Tier 2 compatibility checks or
Tier 3 search.

{docstring Hex.Conway.luebeckConwayPolynomial?}

# The supported-entry witness
%%%
tag := "hex-conway-supported"
%%%

For each supported pair the library commits a {name}`Hex.Conway.SupportedEntry`,
a record bundling the looked-up polynomial with the two facts that make
it a genuine Conway modulus: a primality witness `prime : Hex.Nat.Prime p`
for the field characteristic, and a proof `isSupported` that
{name}`Hex.Conway.luebeckConwayPolynomial?` actually resolves to the
stored polynomial at `(p, n)`. The accessor reads the modulus back out.

{name}`Hex.Conway.SupportedEntry` therefore certifies that a lookup is a
hit, not just that a polynomial exists. The committed witnesses are
named `supportedEntry_p_n` (for example {name}`Hex.Conway.supportedEntry_2_3`).

{docstring Hex.Conway.conwayPoly}

# Worked example
%%%
tag := "hex-conway-worked"
%%%

The block below runs the lookup on the supported pair `(2, 3)` (the
Conway polynomial `C(2, 3) = 1 + x + x³` over `𝔽₂`) and on two
unsupported pairs.

```lean
open Hex Hex.Conway

namespace HexConwayChapter

-- The committed table stores C(2,3) ascending by
-- degree: 1 + x + x³.
#guard luebeckConwayCoeffs? 2 3 = some [1, 1, 0, 1]

-- The lookup builds the FpPoly from those
-- coefficients, hitting the committed literal.
#guard luebeckConwayPolynomial? 2 3 =
  some luebeckConwayPolynomial_2_3

-- The SupportedEntry witness packages the same hit,
-- and conwayPoly reads the modulus back out.
#guard supportedEntry_2_3.poly =
  luebeckConwayPolynomial_2_3
#guard conwayPoly 2 3 supportedEntry_2_3 =
  luebeckConwayPolynomial_2_3

-- Unsupported pairs return none rather than
-- searching: n outside {1..6}, or n = 0.
#guard luebeckConwayPolynomial? 2 7 =
  (none : Option (FpPoly 2))
#guard luebeckConwayPolynomial? 2 0 =
  (none : Option (FpPoly 2))

end HexConwayChapter
```

# Key correctness theorem
%%%
tag := "hex-conway-correctness"
%%%

The point of committing a table rather than computing on demand is that
each entry carries a machine-checked irreducibility proof. For every
supported pair the library proves `luebeckConwayPolynomial_p_n_irreducible :
FpPoly.Irreducible luebeckConwayPolynomial_p_n`, discharged by running
the Berlekamp Rabin irreducibility certificate checker
(`Berlekamp.rabinTest_imp_irreducible`) on a committed certificate. The
representative statement for `C(2, 3)`:

{docstring Hex.Conway.luebeckConwayPolynomial_2_3_irreducible}

Because the certificate is checked at elaboration time, the irreducible
factor structure of the committed table is part of the library's
guarantee, not a runtime assertion: a corrupted entry would fail to
typecheck rather than silently return a reducible polynomial.

# Cross-references
%%%
tag := "hex-conway-cross-references"
%%%

`HexConway` is near the top of the finite-field portion of the DAG:

* `HexBerlekamp` is the direct dependency. Its Rabin irreducibility
  test and the soundness theorem `rabinTest_imp_irreducible` (lifting a
  passing certificate to {name}`Hex.FpPoly.Irreducible`) certify every
  committed entry in the
  {ref "hex-conway-correctness"}[correctness section]. The prime-field
  polynomial type {name}`Hex.FpPoly` and its arithmetic are reached
  transitively through it.
* The Tier 2 compatibility proofs (Conway conditions across the
  subfield lattice) and Tier 3 search live in separate libraries above
  this one. This chapter documents only the Tier 1 committed lookup.
* `HexConway` is Mathlib-free and never depends on Mathlib. The Mathlib
  correspondence proofs for the finite-field theory it draws on live in
  the higher layers' `*Mathlib` counterparts, not in this library.
