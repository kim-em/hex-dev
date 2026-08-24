# hex-gfq-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

The Mathlib correspondence layer for
[`hex-gfq`](https://github.com/leanprover/hex-gfq). It puts Mathlib's `Field`
structure, finiteness and cardinality on the executable quotient-field
construction, identifies the canonical Conway fields with Mathlib's
`GaloisField`, and defines the canonical embedding of one committed Conway
field into another. The packed binary model reaches Mathlib through
[`hex-gf2-mathlib`](https://github.com/leanprover/hex-gf2-mathlib), and the
polynomial-level steps route through
[`hex-poly-fp-mathlib`](https://github.com/leanprover/hex-poly-fp-mathlib).

# Quickstart

```toml
[[require]]
name = "hex-gfq-mathlib"
git = "https://github.com/leanprover/hex-gfq-mathlib.git"
rev = "main"
```

```lean
import HexGFqMathlib
open Hex

-- The packed binary Conway field is Mathlib's `GaloisField 2 n`.
noncomputable example (n : Nat) [GFq.PackedGF2Entry n] :
    GF2q n ≃+* GaloisField 2 n :=
  GF2q.equivGaloisField

-- The generic Conway field has the cardinality its name promises.
example {p n : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (h : Conway.SupportedEntry p n) :
    Fintype.card (GFq p n h) = p ^ n :=
  HexGFqMathlib.GFq.fintype_card_eq_pow h
```

# Functionality

- `FiniteField.field`, the Mathlib `Field` instance on
  `GFqField.FiniteField f hf hp hirr`, built from the executable
  `Lean.Grind.Field` laws so the operations stay the executable ones. `npow` is
  pinned to the executable power rather than left at Mathlib's `npowRec`, so
  the two exponentiations on the type cannot diverge.
- `FiniteField.fintype`, `FiniteField.fintype_card` and
  `GFq.fintype_card_eq_pow`, the cardinality chain that runs from the
  reduced-representative subtype up to `p ^ n`.
- `GFq.equivGaloisField`, `GF2q.equivGFq` and `GF2q.equivGaloisField`: the
  generic Conway field against Mathlib's, the packed binary field against the
  generic one, and their composite.
- `ofPolyHom`, `constHom` and `substHom`, the reduction, constant-embedding and
  substitution ring homomorphisms into the executable field. These are what a
  Mathlib construction needing a `RingHom` out of the executable side is
  pointed at.
- `conwayEmbed`, the embedding of the degree-`m` Conway field into the
  degree-`n` one for a committed divisor pair, instantiated at `GF(2^2)` and
  `GF(2^3)` inside `GF(2^6)`, `GF(13)` inside `GF(13^6)`, and `GF(2^4)` inside
  `GF(2^8)`.
- The component lemmas that move
  [`hex-conway`](https://github.com/leanprover/hex-conway)'s executable
  primitivity check towards Mathlib's `orderOf` vocabulary.

# Verification

The executable field carries Mathlib's `Field` structure, and the carrier is
finite with the cardinality its construction promises:

```lean
noncomputable instance field :
    Field (Hex.GFqField.FiniteField f hf hp hirr)

theorem fintype_card_eq_pow (h : Hex.Conway.SupportedEntry p n) :
    Fintype.card (Hex.GFq p n h) = p ^ n
```

The `Fintype` instances are deliberately `noncomputable`, for the same reason
as elsewhere in the family: `p ^ n` elements behind a compiled `Finset.univ` is
a footgun. The `Equiv`s they are built from stay computable.

Cardinality is the whole input to the Mathlib correspondence.
`equivGaloisField` applies `FiniteField.ringEquivOfCardEq`, which asks only
that the two counts agree, so it needs `Fact p.Prime` and `n ≠ 0` as
hypotheses, neither of which the executable side carries:

```lean
noncomputable def equivGaloisField [Fact p.Prime]
    (h : Hex.Conway.SupportedEntry p n) (hn : n ≠ 0) :
    _root_.RingEquiv (Hex.GFq p n h) (GaloisField p n)
```

The packed binary constructor reaches the same place in two legs, the first
built on hex-gf2-mathlib's `GF2n.equiv` and computable, the second inheriting
the choice `ringEquivOfCardEq` makes:

```lean
def equivGFq : RingEquiv (GF2q n) (GFq 2 n h.entry)

noncomputable def equivGaloisField : RingEquiv (GF2q n) (GaloisField 2 n)
```

The subfield embedding is a genuine ring homomorphism, on a committed divisor
pair carrying a `Conway.Compatible` witness rather than a bare `m ∣ n` proof:

```lean
noncomputable def conwayEmbed (p m n : Nat) [Hex.ZMod64.Bounds p]
    [Hex.ZMod64.PrimeModulus p]
    (hm : Hex.Conway.SupportedEntry p m) (hn : Hex.Conway.SupportedEntry p n)
    (hcompat : Hex.Conway.Compatible p m n hm hn) :
    Hex.GFq p m hm →+* Hex.GFq p n hn
```

`Compatible` is the decidable check that composing `C(p, m)` with
`Conway.normX` reduces to zero, and `substHom_conwayPoly_eq_zero` promotes that
`Bool` to the well-definedness input the embedding needs.

Be clear about what `normX` is not. It is a computed representative, the
product of `n / m` successive Frobenius images of the residue of `x`, reduced
at each step. Reading it as the field norm `α ^ ((p^n - 1) / (p^m - 1))` is the
design rationale for the definition, not a theorem proved here or in hex-conway,
which is explicit that two evaluation and Frobenius bridges are missing first.
Nothing in this package depends on that reading; the root property is what the
embedding uses.

The primitivity transport is likewise partial. `ofPolyHom_linPowMod`,
`ofPolyHom_digitPowMod`, `ofPolyHom_eq_one_iff`, `mathlibPrime_of_hexPrime` and
`mem_of_prime_dvd_primePowerProduct` are the ingredients Mathlib's
`orderOf_eq_of_pow_and_pow_div_prime` needs, each carried across `ofPolyHom`
separately. But no declaration here consumes a `Conway.Primitive` witness or
produces the per-prime hypothesis function that theorem quantifies over, so the
glue from `Primitive.check` to those hypotheses does not exist yet, and the
per-entry conclusion `orderOf α = p ^ n - 1` is correspondingly not assembled.

Use [`hex-gfq`](https://github.com/leanprover/hex-gfq) alone for computation;
this package is for theorem statements and interoperability involving Mathlib.
See the [SPEC](SPEC/hex-gfq-mathlib.md) for the representation choice and the
proof strategy behind each equivalence.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
