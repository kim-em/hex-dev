# hex-conway

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra
library for Lean 4. The aim is fast executable code, fully verified, built
with spec-driven development.

A database of Conway polynomials for Lean 4, without Mathlib. Conway
polynomials are the canonical irreducible polynomials `C(p, n)` used to present
`GF(p^n)` so that the subfield embeddings agree with each other. This package
commits a slice of Frank Lübeck's table as ordinary Lean data and proves that
each committed entry is irreducible, primitive, and compatible with its
divisor-degree entries. It builds on
[`hex-berlekamp`](https://github.com/leanprover/hex-berlekamp) for
irreducibility certificates and
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
  is the committed table, generated into ordinary Lean code. It covers 38
  entries: `p` in `2, 3, 5, 7, 11, 13`, to degree `6` for the odd primes and to
  degree `8` for `p = 2`.
- `SupportedEntry p n` packages a table hit with the primality witness and the
  proof that the lookup resolves to it. It cannot be built for an uncommitted
  pair, which is how `conwayPoly p n h` stays total only where the table
  covers. Each committed pair has a `supportedEntry_p_n`.
- `conwayPoly` returns the modulus, and `conwayPoly_irreducible`,
  `conwayPoly_nonconstant` and `conwayPoly_monic` are the facts a field
  construction needs.
- `Compatible p m n hm hn` is the decidable divisor-compatibility statement,
  computed by `compatCheck`. `subfieldGen` names the norm element it is about.
- `Primitive p n h qs es fullDigits perPrimeDigits` is primitivity, computed by
  `primitiveCheck`, which validates the supplied factorization of `p^n - 1`
  before running the two power conditions.
- `rebuild_luebeckConwayPolynomial?` regenerates the coefficient table from the
  cached Lübeck slice, and `#conway_entry_source` renders the literal, the
  monic and degree facts, the table-hit lemma, and the Rabin certificate that a
  new entry needs. Neither runs during a build.

# Verification

Every one of the 38 committed entries carries an irreducibility certificate
that the kernel replays; `native_decide` is not used anywhere. The aggregate
dispatch theorem is `luebeckConwayPolynomial?_irreducible`, and the API-facing
form is

```lean
theorem conwayPoly_irreducible
    (p n : Nat) [ZMod64.Bounds p] (h : SupportedEntry p n) :
    FpPoly.Irreducible (conwayPoly p n h)
```

Divisor compatibility is proved for every committed pair `(p, m, n)` with
`m ∣ n` and `m < n`: 52 theorems `compat_p_m_n`, plus `not_compatible_11_4_6`
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

Primitivity is proved for the 37 committed entries with `p^n > 2`, one theorem
`primitive_p_n` each. `C(2, 1)` is excluded because its multiplicative group is
trivial. Because `primitiveCheck` validates that the supplied divisors multiply
back to `p^n - 1`, a short prime list cannot make the check pass.

On-demand search for pairs the table does not cover is specified but not
implemented. There is no API for it, and no `(p, n)` outside the committed
slice can be constructed. The transport of primitivity into Mathlib's
`orderOf` language, and the canonical embedding `conwayEmbed`, live in
[`hex-gfq-mathlib`](https://github.com/leanprover/hex-gfq-mathlib). See the
[SPEC](SPEC/hex-conway.md) for the tier boundaries and the proof budget that
sets the size of the committed slice.

# Contributing

Development happens in the
[`hex-dev`](https://github.com/kim-em/hex-dev) monorepo, not in this published
mirror. Contributions are welcome as pull requests to the `SPEC/` directory:
describe the behavior you want and leave the implementation to the maintainer.
