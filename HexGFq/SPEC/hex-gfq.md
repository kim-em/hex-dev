# hex-gfq (convenience wrapper, depends on hex-gfq-field + hex-conway + hex-gf2)

User-facing constructors for canonical finite fields. This is the layer
where the library chooses the irreducible polynomial for you.

For all primes `p`, `GFq p n` uses the same generic quotient-field
construction from `hex-gfq-field`, instantiated with the Conway
polynomial from `hex-conway`. For `p = 2`, this library additionally
provides an optimized convenience constructor built on `hex-gf2`.

```lean
/-- Canonical finite field for a committed Conway-table entry, always using the
    generic quotient-field representation from `hex-gfq-field`. In particular
    `GFq 2 n` does NOT switch to the packed `hex-gf2` representation. -/
abbrev GFq (p n : Nat) [ZMod64.Bounds p] (h : Conway.SupportedEntry p n) : Type

/-- The same field with the committed entry found by instance synthesis, which
    is the spelling users want. -/
abbrev GFqC (p n : Nat) [ZMod64.Bounds p] [h : GFq.CommittedEntry p n] : Type

/-- Optimized canonical `GF(2^n)`, using the Conway polynomial chosen by
    `hex-conway` but represented with the packed `hex-gf2` backend. -/
abbrev GF2q (n : Nat) [h : GFq.PackedGF2Entry n] : Type
```

The evidence is explicit in the type rather than assumed. `GFq` takes a
`Conway.SupportedEntry p n`, which packages the table hit with its primality
and irreducibility proofs and cannot be constructed for an uncommitted pair.
`GFqC` and `GF2q` take the same evidence through instance synthesis, so the
user writes the pair and the instance supplies the witness.

That is why there is no `conwayPoly p n` with two arguments: a total function
would have to invent a modulus for pairs the table does not cover, and
`hex-conway` is explicit that `conwayPoly` should be total only for committed
entries.

**Coverage.** The committed table runs over `p` in `2, 3, 5, 7, 11, 13`, to
degree `6` for the odd primes and to degree `8` for `p = 2`. Every one of those
pairs has a `CommittedEntry` instance; the binary column additionally has
`PackedGF2Entry` instances, so `GF2q n` resolves for `n` in `1` to `8`. Outside
that range the constructors fail at instance synthesis, which is the intended
behaviour: there is no junk field.

API intent:

- `GFqC p n` is the spelling to reach for; `GFq p n h` is for proofs that need
  to name the witness.
- `GF2q n` is the specialized `p = 2` constructor using the packed
  representation.
- `GF2q n ≃+* GFq 2 n`, so users can move between the optimized and generic
  `p = 2` models without changing the mathematics. That equivalence is
  `GF2q.equivGFq` and it lives in `hex-gfq-mathlib`, not here: `≃+*` is
  Mathlib's `RingEquiv`, and this library is Mathlib-free. The Mathlib-free
  one-way map `GF2q.toGFq` lives here.
- Both constructors choose the modulus automatically via Conway polynomials, so
  the user supplies neither a polynomial nor an irreducibility proof.

The user writes `GFqC 3 5` and gets the canonical `GF(3^5)`. The user writes
`GF2q 8` and gets the optimized canonical `GF(2^8)` backed by packed bitwise
arithmetic. For non-Conway models, including AES's `x^8 + x^4 + x^3 + x + 1`,
which is a different irreducible from the Conway polynomial at degree 8, use
`FiniteField` directly from hex-gfq-field or `GF2n`/`GF2nPoly` directly from
hex-gf2.

## External comparators

No external comparator is required.

**Justification:** `structural-layer` per
`SPEC/benchmarking.md §"Comparator naming"`. HexGFq is a
convenience wrapper that selects the Conway polynomial from
HexConway and constructs `FiniteField p (conwayPoly p n) ...`
using HexGFqField's generic quotient-field machinery (or
`GF2q` via HexGF2's packed representation for `p = 2`). The
runtime cost is dominated by the underlying quotient-field
arithmetic, which is covered by HexGFqField's external comparator
declaration (FLINT `fq_default`, informational); the `GF2q` path
is covered by HexGF2's external comparator declaration
(NTL `GF2X`, informational). HexGFq itself contributes only the
modulus-selection step, which is a Conway-table lookup and a
constructor call — not an algorithmic surface that benefits from
an independent external reference.
