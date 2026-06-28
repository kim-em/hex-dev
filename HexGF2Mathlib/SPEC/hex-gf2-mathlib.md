# hex-gf2-mathlib (depends on hex-gf2 + hex-poly-fp + hex-gfq-field + Mathlib)

Proves ring equivalences between hex-gf2's packed bitwise types and
the generic finite field constructions:

- `GF2Poly ≃+* FpPoly 2` — unpack/repack between packed bitwise
  representation and the generic `DensePoly (ZMod64 2)` representation.
- `GF2n n irr ≃+* FiniteField 2 f hf hirr` — single-word GF(2^n) elements
  correspond to the quotient-ring field construction from hex-gfq-field.
- `GF2nPoly f hirr ≃+* FiniteField 2 f hf hirr` — multi-word GF(2^n)
  elements (for n >= 64) similarly correspond.
- Bridge-side finiteness/cardinality for `GF2n` and `GF2nPoly`, obtained by
  transporting `Fintype` and cardinality facts across those equivalences.

These transfer via `GF2Poly ≃+* FpPoly 2`, so Mathlib theorems about
finite fields apply to the packed representations. In particular, the
computational `HexGF2` library stays Mathlib-free while `HexGF2Mathlib`
owns the `Fintype` and cardinality surface promised to downstream proof
libraries.
