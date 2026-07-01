/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexGFq.Basic
import HexGFqMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexGFq: canonical finite-field constructors" =>
%%%
tag := "hex-gfq"
%%%

# Introduction
%%%
tag := "hex-gfq-intro"
%%%

`HexGFq` packages the committed Conway-table entries of
{ref "hex-conway"}[`HexConway`] as ready-to-use field types, so a caller
who wants `GF(pⁿ)` for a supported pair `(p, n)` never has to supply a
modulus or an irreducibility proof by hand. It builds on the executable
field {ref "hex-gfq-field"}[`HexGFqField`], the Conway lookup
`HexConway`, and the packed characteristic-two field `HexGF2`.

It exposes two parallel families of constructors. The *generic* family
builds every field as the `HexGFqField` quotient `` `Fₚ[x] / (f)` `` with
`f` the committed Conway modulus, and works for every committed `(p, n)`.
The *packed* characteristic-two family, for committed binary entries,
instead routes through the single-word `HexGF2` representation, trading
the generic quotient for machine-word arithmetic while certifying, at
elaboration time, that the packed modulus is the same Conway polynomial.
`HexGFq` is Mathlib-free; everything below typechecks against the
executable libraries only.

# The committed-entry mechanism
%%%
tag := "hex-gfq-committed"
%%%

The generic constructors need a {name}`Hex.Conway.SupportedEntry`, the
`HexConway` witness bundling a Conway modulus with its primality and
irreducibility proofs. Passing that witness explicitly everywhere is
verbose, so `HexGFq` makes it available through instance synthesis with a
one-method class.

{name}`Hex.Conway.CommittedEntry` carries a single field `entry`, the
committed {name}`Hex.Conway.SupportedEntry` for the pair `(p, n)`. The
library commits one instance per committed table cell, named
`committedEntry_p_n` (for example `committedEntry_2_3`), covering
`p ∈ {2, 3, 5, 7, 11, 13}` and `n ∈ {1, …, 6}`. With the instance in
scope, the short field spelling resolves the witness automatically; where
a proof needs to name the witness, the explicit form still takes it as an
argument.

# Generic constructors
%%%
tag := "hex-gfq-generic"
%%%

The headline type is {name}`Hex.GFq`: given an explicit
`Hex.Conway.SupportedEntry p n`, it is the `HexGFqField` finite field over
the committed Conway modulus, with the positive-degree, primality, and
irreducibility hypotheses discharged from the entry. Its ergonomic
sibling {name}`Hex.GFqC` is the same field with the entry resolved by
{name}`Hex.Conway.CommittedEntry` synthesis, so `GFqC 2 3` denotes
`GF(8)` with no further arguments.

Elements are built by reducing a raw `FpPoly` into the field and read
back through the canonical representative projection. The generic
constructor:

{docstring Hex.GFq.ofPoly}

The committed-entry constructor delegates to it, resolving the witness
from the ambient instance:

{docstring Hex.GFqC.ofPoly}

A family of `*_eq_gfq` lemmas characterises the `GFqC` spelling against
the explicit `GFq` one, so a proof may always unfold the convenience
spelling back to the entry-explicit form. The modulus delegation is
representative:

{docstring Hex.GFqC.modulus_eq_gfq}

Both families provide the full executable field API: `repr`, the ring and
field operations, and the Frobenius endomorphism `a ↦ aᵖ` as the `p`-th
power map.

{docstring Hex.GFq.frob}

# Packed characteristic-two constructors
%%%
tag := "hex-gfq-packed"
%%%

For committed binary entries `(2, n)`, the generic quotient is heavier
than necessary: the field has a single-word packed representation in
`HexGF2`. `HexGFq` exposes that fast path alongside the generic one and
proves the two agree.

The translation from a packed single-word modulus to the generic
`FpPoly 2` view is:

{docstring Hex.Conway.packedGF2FpPoly}

A committed binary entry that also admits the packed view is recorded by
the class {name}`Hex.Conway.PackedGF2Entry`. Its fields bundle the
`HexConway` `SupportedEntry`, the packed lower-word modulus `lower`, the
extension-degree bounds `0 < n < 64`, the certified irreducibility of the
packed modulus, and (crucially) `conway_eq_packed`, the proof that the
committed Conway polynomial *equals* the packed modulus viewed as an
`FpPoly 2`. That equality is what lets the optimized field stand in for
the canonical one without changing the mathematics. The committed
instances are named `packedGF2Entry_2_n`.

The optimized field itself is {name}`Hex.GF2q`: for a committed
`PackedGF2Entry n`, the single-word `HexGF2` field `GF2n` with that
modulus. Words enter and leave through:

{docstring Hex.GF2q.ofWord}

and the translation into the generic model (packing's correctness made
executable) is:

{docstring Hex.GF2q.toGFq}

# Worked example
%%%
tag := "hex-gfq-worked"
%%%

The committed pair `(2, 3)` gives `GF(8) = 𝔽₂[x] / (x³ + x + 1)`, the
Conway field `C(2, 3)`. The block below picks up its field type two
ways (the generic `GFqC 2 3` and the packed `GF2q 3`), then exercises the
packed constructors, where elements are machine words whose bits are the
polynomial coefficients (bit `i` is the coefficient of `xⁱ`). Each
`#guard` is checked when the chapter builds.

```lean
open Hex

namespace HexGFqChapter

-- Both spellings of GF(8) resolve via instance
-- synthesis on the committed (2, 3) entry.
#check (GFqC 2 3)
#check (GF2q 3)

-- Packed elements of GF(8); bit i is the xⁱ coeff.
abbrev E := GF2q 3
def ofW (w : UInt64) : E := GF2q.ofWord w

-- x = 0b010, x² = 0b100.
-- x · x² = x³ ≡ x + 1 = 0b011, since x³+x+1 = 0.
#guard GF2q.repr (ofW 2 * ofW 4) = 3
-- x · x = x² = 0b100.
#guard GF2q.repr (ofW 2 * ofW 2) = 4
-- x⁴ = x·x³ ≡ x²+x = 0b110.
#guard GF2q.repr (ofW 4 * ofW 4) = 6
-- Addition is XOR: (x+1) + (x²+1) = x²+x = 0b110.
#guard GF2q.repr (ofW 3 + ofW 5) = 6
-- x⁻¹ = x²+1 = 0b101, since x·(x²+1) = x³+x = 1.
#guard GF2q.repr (ofW 2)⁻¹ = 5
#guard GF2q.repr (ofW 2 * (ofW 2)⁻¹) = 1

end HexGFqChapter
```

# Key correctness: Lean-checked irreducibility
%%%
tag := "hex-gfq-correctness"
%%%

A finite field exists only when its modulus is irreducible, so every
constructor in this library ultimately rests on an irreducibility proof.
For the generic constructors that proof is the `HexConway` entry's; for
the packed constructors it is a separate certificate over the `HexGF2`
`GF2Poly.Irreducible` predicate, discharged by `decide` on a checkable
certificate, never by `native_decide`. The degree-one case is small
enough to prove by exhausting the two monic linear polynomials over
`𝔽₂`:

{docstring Hex.Conway.packedGF2Entry_2_1_irreducible}

Higher-degree committed entries are certified the same way through the
`HexGF2` certificate checker. Because the check runs at elaboration time,
a corrupted packed modulus would fail to typecheck rather than silently
producing a non-field, so the irreducible-modulus guarantee is checked
when the library compiles, not a runtime assertion.

# The Mathlib correspondence
%%%
tag := "hex-gfq-mathlib"
%%%

Everything above is executable and Mathlib-free. `HexGFqMathlib`
connects it to Mathlib: for prime `p`, the executable field
{name}`Hex.GFq` is ring-isomorphic to Mathlib's `GaloisField p n`, with
`p ^ n` elements.

{docstring HexGFqMathlib.GFq.equivGaloisField}

{docstring HexGFqMathlib.GFq.fintype_card_eq_pow}

{docstring HexGFqMathlib.GFq.card_eq_galoisField_card}

# Cross-references
%%%
tag := "hex-gfq-cross-references"
%%%

`HexGFq` is the aggregator of the finite-field constructor libraries:

* {ref "hex-conway"}[`HexConway`] supplies the committed Conway moduli
  and their {name}`Hex.Conway.SupportedEntry` witnesses; each
  {name}`Hex.Conway.CommittedEntry` instance wraps one.
* {ref "hex-gfq-field"}[`HexGFqField`] (over
  {ref "hex-gfq-ring"}[`HexGFqRing`]) is the generic quotient field
  backing {name}`Hex.GFq` and {name}`Hex.GFqC`; every generic operation
  delegates to it.
* `HexGF2` provides the single-word packed field `GF2n` backing
  {name}`Hex.GF2q`, together with the `GF2Poly.Irreducible` predicate the
  packed certificates discharge.

`HexGFq` is Mathlib-free; its Mathlib correspondence
({ref "hex-gfq-mathlib"}[above], via `HexGFqMathlib`) identifies the
executable field with Mathlib's `GaloisField`.
