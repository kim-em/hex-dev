# hex-conway

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

A database of Conway polynomials for Lean 4, without Mathlib. Conway
polynomials are the canonical irreducible polynomials `C(p, n)` used to present
`GF(p^n)` so that the subfield embeddings agree with each other. This package
commits a slice of Frank Lübeck's table as ordinary Lean data and proves that
every committed entry is irreducible and primitive, and
every proper divisor-degree pair is compatible. It builds on
[`hex-berlekamp`](https://github.com/leanprover/hex-berlekamp) for
irreducibility certificates,
[`hex-primality`](https://github.com/leanprover/hex-primality) for checked
factor-prime certificates, and
[`hex-gfq-ring`](https://github.com/leanprover/hex-gfq-ring) for the quotient
that compatibility is stated in. The subfield embedding `GFq p m →+* GFq p n`
and the Mathlib-side order statements live in
[`hex-gfq-mathlib`](https://github.com/leanprover/hex-gfq-mathlib).

# Quickstart

```toml
[[require]]
name = "hex-conway"
git = "https://github.com/leanprover/hex-conway.git"
rev = "main"
```

```lean
import HexConway
open Hex Hex.Conway

-- The committed Conway polynomial `C(3, 4)`, with its Tier 1 proofs.
def f : FpPoly 3 := conwayPoly 3 4 supportedEntry_3_4

example : FpPoly.Irreducible f := conwayPoly_irreducible 3 4 supportedEntry_3_4
example : 0 < FpPoly.degree f := conwayPoly_nonconstant 3 4 supportedEntry_3_4
example : DensePoly.Monic f := conwayPoly_monic 3 4 supportedEntry_3_4

-- Tier 2: `C(3, 2)` sits inside `C(3, 4)`, and the generator is primitive.
#check compat_3_2_4
#check primitive_3_4

-- The raw table lookup, which is `none` outside the committed slice.
#check @luebeckConwayPolynomial?
```

# Functionality

- `luebeckConwayPolynomial? (p n : Nat) [ZMod64.Bounds p] : Option (FpPoly p)`
  is the committed table, generated into ordinary Lean code. It covers **594
  entries** in every prime characteristic below 1000:

  | Characteristic | Degrees |
  |---|---|
  | 2 | 1–16 |
  | 3, 5, 7 | 1–8 |
  | 11, 13 | 1–6 |
  | Other primes below 300 | 1–4 |
  | Primes from 300 to 1000 | 1–3 |

  These ranges contain no holes and are closed under positive degree divisors.

- `SupportedEntry p n` packages a table hit with the primality witness and the
  proof that the lookup resolves to it. It cannot be built for an uncommitted
  pair, which is how `conwayPoly p n h` stays total only where the table
  covers. Each committed pair has a `supportedEntry_p_n`.
- `conwayPoly` returns the modulus, and `conwayPoly_irreducible`,
  `conwayPoly_nonconstant` and `conwayPoly_monic` are the facts a field
  construction needs.
- `Compatible p m n hm hn` is the decidable divisor-compatibility statement,
  computed by `compatCheck`. `subfieldGen` names the norm element it is about,
  and `subfieldGen_eq_norm` proves that it is
  `X ^ ((p^n - 1) / (p^m - 1))` in the quotient.
- `Primitive p n h qs es` is primitivity, computed by
  `primitiveCheck`, which validates the supplied factorization of `p^n - 1`
  before running the two power conditions.
- Primitivity and compatibility are exposed as named `primitive_p_n` and
  `compat_p_m_n` facts; they do not have a dispatcher over arbitrary lookup witnesses.
- `supportedPairs` enumerates the exact verified keys. The development
  monorepo's `scripts/conway/scope.json` is the generation input; the shared
  factorization corpus cache is kept separate.
- `scripts/conway/generate.py` in `hex-dev` deterministically regenerates all
  coefficients, certificates, compatibility facts, supported-entry witnesses,
  and Mathlib generator-order specializations. Run it with the pinned Python
  dependencies; `--check` verifies committed output. Ordinary builds neither
  fetch source data nor search for certificates or factorizations.
- `rebuild_luebeckConwayPolynomial?` and `#conway_entry_source` remain available
  as Lean commands for inspecting coefficient and Tier 1 generation. Their
  default input path is relative to the `hex-dev` root; in a mirror checkout,
  supply a cache path with `from`.

# Verification

Every supported entry carries an irreducibility certificate
that the kernel replays; `native_decide` is not used anywhere. The aggregate
dispatch theorem is `luebeckConwayPolynomial?_irreducible`, and the API-facing
form is

```lean
theorem conwayPoly_irreducible
    (p n : Nat) [ZMod64.Bounds p] (h : SupportedEntry p n) :
    FpPoly.Irreducible (conwayPoly p n h)
```

Divisor compatibility is proved for every committed pair `(p, m, n)` with
`m ∣ n` and `m < n`: 522 theorems `compat_p_m_n`, plus `not_compatible_11_4_6`
as a negative control so the check is visibly not vacuous. The `Bool` is
promoted to a statement about field elements, which is the well-definedness
input a subfield embedding needs:

```lean
theorem eval_conwayPoly_subfieldGen_eq_zero
    {p m n : Nat} [ZMod64.Bounds p] [ZMod64.PrimeModulus p]
    (hm : SupportedEntry p m) (hn : SupportedEntry p n)
    (hcompat : Compatible p m n hm hn) :
    FpPoly.Quotient.Internal.eval
        (g := conwayPoly p n hn) (hmonic := conwayPoly_monic p n hn)
        (hg_pos := conwayPoly_degree_pos p n hn)
        (conwayPoly p m hm) (subfieldGen p m n hn) =
      FpPoly.Quotient.zero (g := conwayPoly p n hn)
        (hmonic := conwayPoly_monic p n hn)
        (hg_pos := conwayPoly_degree_pos p n hn)
```

Primitivity has one theorem `primitive_p_n` for every supported entry.
`C(2, 1)` explicitly handles the trivial multiplicative group: the factor list
is empty and the generator has order one. `primitiveCheck` verifies that the
supplied prime powers multiply to `p^n - 1`, so a missing factor cannot silently
weaken the order test. Larger factors use Mathlib-free Pocklington certificates.

The polynomial choice is imported from Lübeck's table. Irreducibility,
primitivity and compatibility do not prove lexicographic minimality.

On-demand search for pairs the table does not cover is specified but not
implemented. There is no API for it, and no `(p, n)` outside the committed
slice can be constructed. The transport of primitivity into Mathlib's
`orderOf` language, and the canonical embedding `conwayEmbed`, live in
[`hex-gfq-mathlib`](https://github.com/leanprover/hex-gfq-mathlib). The scope is selected under a **300-second clean Conway rebuild ceiling**
with dependencies already built, including both verification tiers and all
normal library outputs. The additional Mathlib cost is measured separately.
See the [SPEC](SPEC/hex-conway.md) and the
[measurement report](https://github.com/kim-em/hex-dev/blob/main/reports/hex-conway-performance.md)
for the machine, repeated runs, measured limits and reproduction commands.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
