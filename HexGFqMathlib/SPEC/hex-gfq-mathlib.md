# hex-gfq-mathlib (depends on hex-gfq + hex-gf2-mathlib + Mathlib)

## Correspondence-only classification

This library is a `correspondence-only-layer`.

Computational conformance owners: `HexGFqField`, `HexGF2`
Computational performance owners: `HexGFqField`, `HexGF2`

Supplies the finiteness and cardinality layer for the quotient-field
construction, the Mathlib `Field` instance on it, and the correspondence with
Mathlib's `GaloisField`. It also builds on hex-conway's Tier 2 evidence twice
over: the subfield embedding between committed Conway fields, and the lemmas
needed to transport the executable primitivity check into Mathlib's order
vocabulary.

**Contents:**

- `FiniteField.field` — the Mathlib `Field` instance on
  `GFqField.FiniteField f hf hp hirr`, built through `Field.ofMinimalAxioms`
  from the executable `Lean.Grind.Field`, so the operations stay the executable
  ones.
- `FiniteField.fintype` and `FiniteField.fintype_card :
  Fintype.card (FiniteField f hf hp hirr) = p ^ f.degree`, indexed through the
  reduced-representative subtype.
- `GFq.fintype_card_eq_pow : Fintype.card (GFq p n h) = p ^ n`, which composes
  the above with `conwayPoly_degree`.
- `GFq.equivGaloisField : GFq p n h ≃+* GaloisField p n`.
- `GF2q.equivGFq : GF2q n ≃+* GFq 2 n h.entry`, the packed-to-generic leg.
- `ofPolyHom`, `constHom`, and `substHom`, the reduction, constant-embedding,
  and substitution ring homomorphisms into
  `GFqField.FiniteField f hf hp hirr`, which is what a Mathlib construction
  needing a `RingHom` out of the executable side is pointed at.
- `conwayEmbed : GFq p m →+* GFq p n`, the embedding of the degree-`m` Conway
  field into the degree-`n` one for a committed divisor pair carrying a
  `Conway.Compatible` witness, instantiated at four such pairs.
- `orderOf_gen_of_primitive`, which transports a hex-conway executable
  primitivity certificate to the Mathlib statement that the Conway generator
  has order `p ^ n - 1`, plus named specializations for all thirty-seven
  committed nontrivial entries.

The `Fintype` instances are deliberately `noncomputable`. The carriers have
`p ^ degree f` elements, so a compiled `Finset.univ` over one is a footgun
rather than a feature; the underlying `Equiv`s are computable, which is the
part callers want.

## Representation choice

`GFq p n` is always the generic quotient-field construction from
hex-gfq-field, even when `p = 2`. The optimized `p = 2` constructor is `GF2q n`
from hex-gfq, and it reaches Mathlib in two legs: `GF2q n ≃+* GFq 2 n` from
here, composed with `GFq 2 n ≃+* GaloisField 2 n`, also from here. The first
leg is built on hex-gf2-mathlib's `GF2n.equiv`, which is why this library
depends on it.

## Proof strategy

`equivGaloisField` applies Mathlib's `FiniteField.ringEquivOfCardEq`, which
needs only that the two cardinalities agree. Both are `p ^ n`: Mathlib supplies
`GaloisField.card`, and this library supplies `GFq.fintype_card_eq_pow`. It
therefore needs `[Fact p.Prime]` and `n ≠ 0`, both of which `GaloisField.card`
requires and neither of which the executable side carries, so they are
hypotheses on the equivalence rather than on the field type.

## The Conway subfield embedding

`Subfield.lean` defines the map hex-conway's Tier 2 evidence licenses.
`Conway.normX` is a computed representative: the product of `k = n / m`
successive Frobenius images of the residue of `x`, reduced modulo `C(p, n)` at
each step, structured that way so the kernel can replay it.
`Conway.subfieldGen_eq_norm` proves that its quotient class is the explicit
finite-field norm power `α ^ ((p^n - 1) / (p^m - 1))`;
`eval_conwayPoly_subfieldGen_eq_zero` proves that `C(p, m)` vanishes there,
which is the well-definedness input the embedding needs.

`conwayEmbed` is the resulting ring homomorphism `GFq p m →+* GFq p n`. Its
domain is a committed divisor pair carrying a `Conway.Compatible` witness
rather than a bare `m ∣ n` proof: `Compatible` is the decidable check that
composing `C(p, m)` with `normX` reduces to zero, and that is what makes the
substitution well defined. The multiplicative content is Mathlib's:
`Polynomial.eval₂RingHom` is a ring homomorphism by construction, so all the
Hex side has to supply is that the executable substitution agrees with it,
which is additive and monomial data. `GF(2^2)` and `GF(2^3)` inside `GF(2^6)`,
`GF(13)` inside `GF(13^6)`, and `GF(2^4)` inside `GF(2^8)` are checked here as
examples.

The canonicality statement is exposed directly. `conwayEmbed_X` says that
`conwayEmbed` sends the source class of `X` to `conwayGen`, while
`conwayGen_eq_norm` identifies `conwayGen` with the explicit finite-field norm
power of the target class of `X`. `conwayEmbed_X_eq_norm` combines these into
one theorem for a divisor pair; positivity of `m` follows from the source's
committed entry.

## Primitivity transport

`Primitivity.lean` transports hex-conway's executable order check across
`ofPolyHom`. The check runs on `FpPoly`
representatives with structural powers, while `orderOf` is about Mathlib's `^`
in the field, so each ingredient travels separately: `ofPolyHom_linPowMod` and
`ofPolyHom_digitPowMod` move the powers through `map_mul` and `map_pow`,
`ofPolyHom_eq_one_iff` turns "not one" on a reduced representative into "not
one" in the field, `mathlibPrime_of_hexPrime` converts the Mathlib-free
primality predicate, and `mem_of_prime_dvd_primePowerProduct` shows that a
validated prime-power product lists every prime dividing it, so a short prime
list cannot weaken the test.

`orderOf_gen_of_primitive` unpacks the validated Boolean conjunctions, aligns
each listed prime with its digit witness, transports both power conditions,
and applies Mathlib's `orderOf_eq_of_pow_and_pow_div_prime`. The named
`orderOf_gen_p_n` corollaries expose the resulting `orderOf α = p ^ n - 1`
statement for every committed entry with `p ^ n > 2`.

## Namespaces

Declarations live in `HexGFqMathlib`, except `GF2q.equivGFq`, which extends
`Hex.GF2q` so that it reads as part of the constructor's API at the call site.

## External comparators

No external comparator is required.

**Justification:** `correspondence-only-layer` per
`SPEC/benchmarking.md §"Comparator naming"`. The library introduces no
arithmetic algorithm; it transports facts about constructions implemented
elsewhere. The computational performance owners are hex-gfq-field and hex-gf2,
where those constructions are measured.
