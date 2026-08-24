# hex-gf2-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

The Mathlib correspondence layer for
[`hex-gf2`](https://github.com/leanprover/hex-gf2). It relates the packed
bitwise polynomials and their `GF(2^n)` wrappers to the generic quotient-field
construction from
[`hex-gfq-field`](https://github.com/leanprover/hex-gfq-field), and reaches
Mathlib's `Polynomial (ZMod 2)` by composing with
[`hex-poly-fp-mathlib`](https://github.com/leanprover/hex-poly-fp-mathlib). It
also carries finiteness, cardinality, and Mathlib's `CommRing`,
`EuclideanDomain`, gcd-domain, and `Field` structure on the packed types.

# Quickstart

```toml
[[require]]
name = "hex-gf2-mathlib"
git = "https://github.com/leanprover/hex-gf2-mathlib.git"
rev = "main"
```

```lean
import HexGF2Mathlib
open Hex

-- Packed `F₂[x]` as Mathlib's polynomial ring, with the packed operations kept.
noncomputable example : GF2Poly ≃+* Polynomial (ZMod 2) :=
  HexGF2Mathlib.GF2Poly.equivPolynomial

example (p q : GF2Poly) : p * q = GF2Poly.mul p q := rfl
example (p q : GF2Poly) : p / q = GF2Poly.div p q := rfl
example (p q : GF2Poly) : GCDMonoid.gcd p q = GF2Poly.gcd p q := rfl
example (p q : GF2Poly) :
    EuclideanDomain.gcd p q = GF2Poly.gcd p q :=
  HexGF2Mathlib.GF2Poly.euclidean_gcd_eq_packed p q

-- A single-word `GF(2^n)` is the generic quotient field, and has `2 ^ n` elements.
example {n : Nat} {irr : UInt64} {hn : 0 < n} {hn64 : n < 64}
    {hirr : GF2Poly.Irreducible (GF2Poly.ofUInt64Monic irr n)} :
    Fintype.card (GF2n n irr hn hn64 hirr) = 2 ^ n :=
  HexGF2Mathlib.GF2n.fintype_card
```

# Functionality

- `GF2Poly.equiv` unpacks and repacks between the packed bitwise
  representation and the generic dense one, with `toFpPoly` and `ofFpPoly` as
  the named directions and transport lemmas for coefficients, degree,
  arithmetic and irreducibility.
- `GF2Poly.equivPolynomial` composes that with the prime-field equivalence from
  [`hex-poly-fp-mathlib`](https://github.com/leanprover/hex-poly-fp-mathlib),
  which is where a Mathlib user starts.
- `GF2n.equiv` and `GF2nPoly.equiv` identify the single-word and
  arbitrary-degree packed `GF(2^n)` wrappers with the generic
  `GFqField.FiniteField` over the transported modulus.
- `Fintype` instances for both wrappers, their cardinality theorems, and the
  computable `finEquiv` indexings they are built from.
- `CommRing Hex.GF2Poly`, `EuclideanDomain Hex.GF2Poly`, a `GCDMonoid` whose
  gcd is definitionally `GF2Poly.gcd`, `Field (Hex.GF2n n irr hn hn64 hirr)`,
  and `Field (Hex.GF2nPoly f hirr)` for a nonconstant modulus. The `GF2n`
  instance keeps its packed multiplication, negation, inversion, subtraction,
  and division definitions; the constructor supplies the remaining derived
  hierarchy operations.

The equivalences are Mathlib's `≃+*`, not a project-local record, so they
compose with other `RingEquiv`s and are accepted by Mathlib's equivalence APIs.

# Verification

The equivalences are the content. The packed polynomial representation
corresponds to the generic one, and composing reaches Mathlib:

```lean
def equiv : Hex.GF2Poly ≃+* Hex.FpPoly 2

noncomputable def equivPolynomial : Hex.GF2Poly ≃+* Polynomial (ZMod 2)
```

`equivPolynomial` is `noncomputable` because Mathlib's polynomial
multiplication is; the packed side stays executable. The algebraic instances
keep the executable operations rather than transported copies, so
`p * q = GF2Poly.mul p q`, `p / q = GF2Poly.div p q`, and
`GCDMonoid.gcd p q = GF2Poly.gcd p q` close by `rfl`. The Euclidean instance
also makes Mathlib's Bezout, principal-ideal, and unique-factorization
interfaces available on the packed type. The stated
`GF2Poly.euclidean_gcd_eq_packed` lemma identifies the gcd in Mathlib's
recursive Bezout theorem with the executable packed gcd.

The single-word wrapper, in namespace `HexGF2Mathlib.GF2n`:

```lean
def equiv : Hex.GF2n n irr hn hn64 hirr ≃+*
    GenericFiniteField (n := n) (irr := irr) (hn := hn) (hn64 := hn64) (hirr := hirr)

theorem fintype_card :
    Fintype.card (Hex.GF2n n irr hn hn64 hirr) = 2 ^ n
```

The arbitrary-degree wrapper, in namespace `HexGF2Mathlib.GF2nPoly`:

```lean
def equiv : Hex.GF2nPoly f hirr ≃+* GenericFiniteField (f := f) (hirr := hirr) (hdeg := hdeg)

theorem fintype_card :
    Fintype.card (Hex.GF2nPoly f hirr) = 2 ^ f.degree
```

The cardinalities are read off the representation, `GF2n` from its `val` bound
and `GF2nPoly` through its reduced-representative subtype, rather than
transported across the ring equivalence. The `Fintype` instances are
deliberately `noncomputable`: the carriers have `2 ^ n` elements, so a compiled
`Finset.univ` over one is a footgun. The `Equiv`s underneath stay computable.

The `GF2n` field instance needs no additional hypothesis because its type
already carries `0 < n`. The `Field` instance on `GF2nPoly` takes
`Fact (0 < f.degree)`, and the hypothesis is not redundant:
`GF2Poly.Irreducible` admits the constant `1`, and the quotient by a constant
is the trivial ring where `0 = 1`.

Use [`hex-gf2`](https://github.com/leanprover/hex-gf2) alone for computation;
this package is for theorem statements and interoperability involving Mathlib.
See the [SPEC](SPEC/hex-gf2-mathlib.md) for the correspondence contract and the
reason the finiteness argument does not go through the ring equivalence.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
