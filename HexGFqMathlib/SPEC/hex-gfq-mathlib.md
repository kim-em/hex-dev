# hex-gfq-mathlib (depends on hex-gfq + hex-gf2-mathlib + Mathlib)

Supplies the finiteness and cardinality layer for the quotient-field
construction, the Mathlib `Field` instance on it, and the correspondence with
Mathlib's `GaloisField`.

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

## Namespaces

Declarations live in `HexGFqMathlib`, except `GF2q.equivGFq`, which extends
`Hex.GF2q` so that it reads as part of the constructor's API at the call site.

## External comparators

No external comparator is required.

**Justification:** `proof-only-layer` per
`SPEC/benchmarking.md §"Comparator naming"`. The library introduces no
arithmetic algorithm; it transports facts about constructions whose performance
is measured in hex-gfq-field and hex-gf2.
