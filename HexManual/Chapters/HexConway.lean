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
search for entries beyond the committed table. `HexConway` currently
implements Tier 1 only: it exposes the imported
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
`p ∈ {2, 3, 5, 7, 11, 13}`, running to `n = 6` for the odd primes and
to `n = 8` for `p = 2`, so `GF(2⁸)` is a committed Conway field. Every
other pair returns `none` rather than triggering Tier 2 compatibility
checks or Tier 3 search.

The binary column runs further because cost decides the scope: the
committed entries carry Rabin certificates that the kernel replays, and
that replay is cheapest over `𝔽₂`, where every residue is one bit. The
scope is therefore a maximum degree per prime rather than one bound for
all of them, and widening it is a matter of measuring rather than of
finding new mathematics.

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
-- searching. The binary column runs to degree 8,
-- the odd primes to 6.
#guard luebeckConwayPolynomial? 2 8 =
  some luebeckConwayPolynomial_2_8
#guard luebeckConwayPolynomial? 2 9 =
  (none : Option (FpPoly 2))
#guard luebeckConwayPolynomial? 3 7 =
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
therefore not a hand edit. Two commands do it.

`rebuild_luebeckConwayPolynomial?` regenerates the coefficient table. It
reads the committed cache, keeps the entries inside a requested scope,
and offers the regenerated definition as a `Try this:` replacement for
the definition written immediately below it:

```
rebuild_luebeckConwayPolynomial? scope [2:8, 3:6, 5:6, 7:6, 11:6, 13:6]
```

The scope is a maximum degree per prime, which is what makes the binary
column reach `n = 8` while the odd primes stop at `n = 6`. The emitted
replacement carries that invocation commented out directly above the
definition, so the next reader can see which scope produced the
committed table and re-run it without reconstructing the arguments.

`#conway_entry_source p n` prints the per-entry block: the polynomial
literal, its monicity and degree lemmas, the Rabin certificate, and the
irreducibility proof that replays it. The coefficients come from the
cache rather than from the caller, so the command cannot be talked into
emitting a valid certificate under a mislabelled `C(p, n)`.

Neither command touches the network. The cache itself is refreshed from
Lübeck's published table by
`scripts/oracle/update_luebeck_conway_cache.py`, which is the only step
that does, so a rebuild is reproducible offline and its output is a pure
function of the cache and the scope.

Widening the scope is a cost decision, not a mathematical one. The
kernel replays each certificate at elaboration time, and that replay is
what the scope is measured against; `reports/hex-conway-performance.md`
records the per-entry cost that set the current bounds.

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
* Tier 2 and Tier 3 belong to this library and are not yet implemented.
  Until Tier 2 lands, what Lean checks about a committed entry is that
  it is monic, irreducible, and of the requested degree. That it is the
  *Conway* polynomial for its pair, rather than some other irreducible
  of the same degree, rests on the imported Lübeck table and is checked
  outside Lean by the conformance oracle. Nothing downstream is weakened
  by this: {ref "hex-gfq"}[`GFq p n`] is a genuine field of order `pⁿ`
  either way. What is not yet available is the compatibility across the
  subfield lattice that motivates the Conway choice in the first place.
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
