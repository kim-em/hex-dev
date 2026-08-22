# hex-gfq

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

Canonical finite fields for Lean 4, without Mathlib. This is the layer that
picks the irreducible polynomial for you: write `GFqC 3 5` and get `GF(3^5)`
presented by its Conway polynomial, with no modulus and no irreducibility proof
to supply. It combines
[`hex-gfq-field`](https://github.com/leanprover/hex-gfq-field) for the generic
quotient-field construction,
[`hex-conway`](https://github.com/leanprover/hex-conway) for the modulus, and
[`hex-gf2`](https://github.com/leanprover/hex-gf2) for a packed binary backend.
The ring equivalence between the two binary models, and the correspondence with
Mathlib's finite fields, live in
[`hex-gfq-mathlib`](https://github.com/leanprover/hex-gfq-mathlib).

# Quickstart

```toml
[[require]]
name = "hex-gfq"
git = "https://github.com/leanprover/hex-gfq.git"
rev = "main"
```

```lean
import HexGFq
open Hex

-- Canonical `GF(3^5)`; instance search picks the committed Conway entry.
abbrev F : Type := GFqC 3 5

def α : F := GFqC.ofPoly #p[0, 1]
def β : F := α ^ 5 + α + 1

example : GFqC.frob α = α ^ 3 := GFqC.frob_eq_pow α

-- Canonical `GF(2^8)` on the packed bitwise backend, same Conway modulus.
abbrev B : Type := GF2q 8

def b : B := GF2q.ofWord 0x53
def c : B := b * b + 1
def d := GF2q.toGFq c
```

# Functionality

- `GFqC p n` is the spelling to reach for. It resolves through a
  `GFq.CommittedEntry` instance, one per committed Conway pair: `p` in
  `2, 3, 5, 7, 11, 13`, to degree `6` for the odd primes and to degree `8` for
  `p = 2`. Outside that range there is no instance, so the constructor fails at
  synthesis rather than inventing a field.
- `GFq p n h` takes the `Conway.SupportedEntry` explicitly, for proofs that
  need to name the witness. `GFqC` is defined as `GFq p n h.entry`.
- `GFq.ofPoly` and `GFq.repr` move between polynomials and field elements, with
  `repr_add`, `repr_mul`, `repr_pow`, `repr_inv_zero` and the rest reducing a
  representative to a `GFqRing.reduceMod` of the Conway modulus. `GFq.frob` is
  the `p`-th power map. `GFqC` mirrors all of it.
- `GF2q n` is the optimized characteristic-two constructor: the same Conway
  modulus, represented by `hex-gf2`'s single-word packed `GF2n`. It resolves
  for `n` from `1` to `8` through `GFq.PackedGF2Entry`. `GF2q.ofWord` and
  `GF2q.repr` are the packed-word views.
- `GF2q.toGFq` maps the packed model into the generic `GFq 2 n` model for the
  same entry. It is one-way here, since the ring equivalence is Mathlib's
  `≃+*`; the two-sided `GF2q.equivGFq` is in
  [`hex-gfq-mathlib`](https://github.com/leanprover/hex-gfq-mathlib).

# Verification

The field type is built directly from the Conway table's proofs, so a `GFq`
that elaborates is a field:

```lean
abbrev GFq (p n : Nat) [ZMod64.Bounds p] (h : Conway.SupportedEntry p n) : Type :=
  GFqField.FiniteField (Conway.conwayPoly p n h)
    (Conway.conwayPoly_nonconstant p n h)
    h.prime
    (Conway.conwayPoly_irreducible p n h)
```

The field laws come with it: `GFq.mul_inv_cancel`, `GFq.inv_mul_cancel`,
`GFq.div_eq_mul_inv` and `GFq.inv_zero` restate
[`hex-gfq-field`](https://github.com/leanprover/hex-gfq-field)'s results at the
Conway-backed type, and `GFq.ext` says two elements agree exactly when their
representatives do.

The packed binary constructor is the part with its own proof obligation. Each
`PackedGF2Entry` instance carries an irreducibility proof for the packed
modulus, replayed from a Rabin certificate by the kernel, and a proof that the
packed word denotes the same polynomial as the committed Conway entry:

```lean
class PackedGF2Entry (n : Nat) where
  entry : SupportedEntry 2 n
  lower : UInt64
  conway_eq_packed : conwayPoly 2 n entry = packedGF2FpPoly lower n
  degree_pos : 0 < n
  degree_lt_word : n < 64
  packed_irreducible : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic lower n)
```

So `GF2q n` and `GFq 2 n` are two presentations of one field, not two fields.
Note that `GF2q 8` uses the Conway modulus `x^8 + x^4 + x^3 + x^2 + 1`, not
AES's `x^8 + x^4 + x^3 + x + 1`; for a non-Conway model use `FiniteField` from
[`hex-gfq-field`](https://github.com/leanprover/hex-gfq-field) or `GF2n`
directly from [`hex-gf2`](https://github.com/leanprover/hex-gf2). See the
[SPEC](SPEC/hex-gfq.md) for the coverage table and the reason `conwayPoly` is
not a two-argument total function.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
