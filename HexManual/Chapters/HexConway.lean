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

#doc (Manual) "HexConway: verified Conway-polynomial lookup" =>
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
search for entries beyond the committed table. `HexConway` implements Tiers 1 and 2: it exposes the imported
[Lübeck](http://www.math.rwth-aachen.de/~Frank.Luebeck/data/ConwayPol/)
Conway table as a lookup with irreducibility, primitivity, and divisor
compatibility proofs. Tier 3 search is unimplemented. The imported choice
comes from Lübeck; these proofs do not establish lexicographic minimality.

`HexConway` is Mathlib-free. It depends on `HexBerlekamp` for Rabin irreducibility certificates and
`HexPrimality` for certificates of the prime factors of multiplicative
orders, together with the prime-field polynomial and quotient libraries. Each supported
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
list and, on a hit, builds the polynomial. The table has 594 verified entries:

* characteristic 2, degrees 1–16;
* characteristics 3, 5 and 7, degrees 1–8;
* characteristics 11 and 13, degrees 1–6;
* other primes below 300, degrees 1–4;
* primes between 300 and 1000, degrees 1–3.

These ranges have no holes and contain every positive divisor of each supported
degree. Every entry has irreducibility and primitivity proofs, and the 522
proper-divisor pairs have compatibility proofs. Other pairs return `none`.
The scope is selected by measuring a complete rebuild against the five-minute
ceiling; the broader source cache does not by itself establish verified support.

{docstring Hex.Conway.luebeckConwayPolynomial?}

# The supported-entry witness
%%%
tag := "hex-conway-supported"
%%%

For each supported pair the library commits a {name}`Hex.Conway.SupportedEntry`,
a record bundling the looked-up polynomial with a primality witness `prime : Hex.Nat.Prime p`
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
Conway polynomial `C(2, 3) = 1 + x + x³` over `𝔽₂`), further supported
binary degrees, and unsupported pairs.

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
-- searching or generating certificates.
#guard luebeckConwayPolynomial? 2 8 =
  some luebeckConwayPolynomial_2_8
#guard luebeckConwayPolynomial? 2 16 =
  some luebeckConwayPolynomial_2_16
#check primitive_2_16
#check compat_2_8_16
#guard luebeckConwayPolynomial? 2 129 =
  (none : Option (FpPoly 2))
#guard luebeckConwayPolynomial? 3 129 =
  (none : Option (FpPoly 3))
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
the Berlekamp Rabin irreducibility certificate checker, whose soundness is
{name}`Hex.Berlekamp.rabinTest_imp_irreducible`, on a committed certificate. The
representative statement for `C(2, 3)`:

{docstring Hex.Conway.luebeckConwayPolynomial_2_3_irreducible}

Because the certificate is checked at elaboration time, the irreducible
factor structure of the committed table is part of the library's
guarantee, not a runtime assertion: a corrupted entry would fail to
typecheck rather than silently return a reducible polynomial.

# Regenerating the table
%%%
tag := "hex-conway-rebuild"
%%%

The committed table is ordinary Lean code that the kernel checks like
any other definition, and it is long: coefficient literals, monicity and
degree lemmas, a Rabin certificate, and an irreducibility proof for
every entry. Changing which slice of Lübeck's data is committed is
therefore not a hand edit. The offline generator
`scripts/conway/generate.py` reads the exact pair list in
`scripts/conway/scope.json` and the pinned source rows in
`scripts/conway/candidates.json`. With the pinned SymPy version installed,
run it to regenerate coefficients, Rabin certificates, factorizations,
primality certificates, primitivity and compatibility proofs, supported-entry
witnesses, Mathlib generator-order and subfield-embedding specializations, and the runtime replay
driver. Its `--check` mode verifies that committed outputs match the inputs.

Only `scripts/conway/import_source.py` fetches Lübeck's source. The source
URL, digest, coefficient convention, and unavailable requested pairs are
recorded alongside the imported rows. The separate shared Lübeck cache
used by the factorization benchmark corpus is unchanged by this pipeline.
The Lean commands `rebuild_luebeckConwayPolynomial?` and
`#conway_entry_source` remain available for inspecting individual entries.
Ordinary builds perform no network requests or certificate searches.

The scope must preserve existing support and contain every positive divisor
of each supported degree. Selection is measured against a 300-second clean
rebuild ceiling for all Conway code and proofs with dependencies already
built. The selected scope must pass three controlled runs. Additional
Mathlib bridge compilation is measured separately. See
`reports/hex-conway-performance.md` for the machine, exact scopes, costs,
and unavailable or expensive candidates.

# Cross-references
%%%
tag := "hex-conway-cross-references"
%%%

`HexConway` is near the top of the finite-field portion of the DAG:

* `HexBerlekamp` is the direct dependency. Its Rabin irreducibility
  test and the soundness theorem
  {name}`Hex.Berlekamp.rabinTest_imp_irreducible` (lifting a
  passing certificate to {name}`Hex.FpPoly.Irreducible`) certify every
  committed entry in the
  {ref "hex-conway-correctness"}[correctness section]. The prime-field
  polynomial type {name}`Hex.FpPoly` and its arithmetic are reached
  transitively through it.
* Tier 2 primitivity and divisor compatibility are implemented in this
  library. Generator-order and subfield-embedding bridges live in
  `HexGFqMathlib`. Tier 3 search is unimplemented.
  Every supported entry has an irreducibility proof and a primitivity
  certificate, including `C(2, 1)` with its trivial multiplicative group.
  Every supported proper-divisor pair has a compatibility theorem. The
  lexicographically minimal choice is imported from Lübeck and checked
  against the pinned source by the conformance oracle; minimality itself
  is not proved in Lean.
* `HexPrimality` supplies Mathlib-free Pocklington certificates for large
  factors of `p^n - 1`, avoiding unbounded trial division during builds.
* `HexConway` is consumed by {ref "hex-gfq"}[`HexGFq`], which turns a
  {name}`Hex.Conway.SupportedEntry` into the canonical field `GFq p n`
  by handing the committed modulus to the quotient construction in
  {ref "hex-gfq-field"}[`HexGFqField`]. The table is what makes that
  field *canonical* rather than merely *a* field of order `pⁿ`: every
  caller naming `GFq 3 4` gets the same modulus, so elements computed in
  one place are comparable with elements computed in another.
* `HexConway` is Mathlib-free and never depends on Mathlib. The Mathlib
  correspondence proofs for the finite-field theory it draws on live in
  the higher layers' `*Mathlib` counterparts, not in this library.
