# hex-gfq-mathlib (depends on hex-gfq + Mathlib)

Provides the finiteness/cardinality layer for the quotient-field
construction and proves `GFq p n ≃+* GaloisField p n` (Mathlib's Galois
field).

Important representation choice:

- `GFq p n` is always the generic quotient-field construction from
  `hex-gfq-field`, even when `p = 2`.
- The optimized `p = 2` constructor is `GF2q n` from `hex-gfq`.
- The `p = 2` optimized path relates to Mathlib by composing
  `GF2q n ≃+* GFq 2 n` with `GFq 2 n ≃+* GaloisField 2 n`.

In particular, this is where `FiniteField p f hf hirr` gets its
`Fintype` instance and cardinality theorem `card = p ^ f.degree`.

Proof strategy: apply `FiniteField.ringEquivOfCardEq` from Mathlib,
which just needs `Fintype.card (GFq p n) = Fintype.card (GaloisField p n)`.
Both sides equal `p ^ n` — Mathlib has `GaloisField.card` and we need
`card_finiteField` from this bridge layer.
