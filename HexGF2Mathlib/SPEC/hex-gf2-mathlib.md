# hex-gf2-mathlib (depends on hex-gf2 + hex-poly-fp + hex-gfq-field + Mathlib)

Relates hex-gf2's packed bitwise types to the generic finite field
constructions, using Mathlib's `RingEquiv` so the results are accepted by
Mathlib's equivalence APIs and compose with other `RingEquiv`s.

**Contents:**

- `GF2Poly ≃+* FpPoly 2` — unpack/repack between the packed bitwise
  representation and the generic `DensePoly (ZMod64 2)` representation.
- `GF2n n irr ≃+* FiniteField 2 f hf hirr` — single-word `GF(2^n)` elements
  correspond to the quotient-ring field construction from hex-gfq-field.
- `GF2nPoly f hirr ≃+* FiniteField 2 f hf hirr` — multi-word `GF(2^n)`
  elements similarly correspond. `GF2nPoly` accepts any modulus; it is the
  representation to reach for when the degree does not fit `GF2n`'s single
  word, rather than one restricted to that case.
- `Fintype` and cardinality for `GF2n` and `GF2nPoly`.

The equivalences are Mathlib's `≃+*`, not a project-local record. Mathlib's
`RingEquiv` asks only for `Mul` and `Add` on each side, which the executable
types already have, so a local copy would avoid nothing and would compose with
nothing, which defeats the purpose of a correspondence library. hex-gfq-mathlib
composes the `GF2n` equivalence with the canonical Conway field through
`RingEquiv.trans`, which is the first leg of the `p = 2` composition that
library's SPEC describes; the second is `GFq 2 n ≃+* GaloisField 2 n`.

**Finiteness.** `GF2n` is indexed by its `val` bound directly, and `GF2nPoly`
through its reduced-representative subtype, rather than by transporting a
`Fintype` across the ring equivalence. Both routes give the same cardinality;
the direct one does not depend on the generic side's own finiteness argument.
The `Equiv`s are computable, the `Fintype` instances deliberately are not: the
carriers have `2 ^ n` elements, so a compiled `Finset.univ` over one is a
footgun rather than a feature.

**What this library does not yet supply.** Neither `GF2n` nor `GF2nPoly` has a
Mathlib `Ring`, `CommRing`, or `Field` instance. A `RingEquiv` does not install
those; they have to be pulled back explicitly, preserving the executable
operations, and that work is outstanding. So the current Mathlib-facing surface
is the equivalences plus `Fintype` and cardinality, and a caller wanting to
apply a Mathlib finite-field theorem must transport across an equivalence by
hand rather than find the instance waiting. `SPEC/design-principles.md` asks
for those instances to live here, and they should.

The computational hex-gf2 library stays Mathlib-free.

## Reaching Mathlib's own types

`GF2Poly ≃+* FpPoly 2` lands on a Hex type, not a Mathlib one. `equivPolynomial`
composes it with `FpPoly p ≃+* Polynomial (ZMod p)` from hex-poly-fp-mathlib to
give `GF2Poly ≃+* Polynomial (ZMod 2)`, which is where a Mathlib user starts. It
is `noncomputable`, since Mathlib's polynomial multiplication is; the packed
side stays executable.

## External comparators

No external comparator is required.

**Justification:** `proof-only-layer` per
`SPEC/benchmarking.md §"Comparator naming"`. This library introduces no new
arithmetic algorithm: it states correspondences between representations that
hex-gf2 and hex-gfq-field implement, and their performance is measured in those
libraries. The encoding and decoding functions it does define exist to state
those correspondences, not as a computational surface anyone races.
