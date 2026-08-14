# hex-gf2-mathlib (depends on hex-gf2 + hex-poly-fp + hex-gfq-field + Mathlib)

Relates hex-gf2's packed bitwise types to the generic finite field
constructions, using Mathlib's `RingEquiv` so that Mathlib's transport
machinery applies to the results.

**Contents:**

- `GF2Poly ≃+* FpPoly 2` — unpack/repack between the packed bitwise
  representation and the generic `DensePoly (ZMod64 2)` representation.
- `GF2n n irr ≃+* FiniteField 2 f hf hirr` — single-word `GF(2^n)` elements
  correspond to the quotient-ring field construction from hex-gfq-field.
- `GF2nPoly f hirr ≃+* FiniteField 2 f hf hirr` — multi-word `GF(2^n)`
  elements (for `n ≥ 64`) similarly correspond.
- `Fintype` and cardinality for `GF2n` and `GF2nPoly`.

The equivalences are Mathlib's `≃+*`, not a project-local record. Mathlib's
`RingEquiv` asks only for `Mul` and `Add` on each side, which the executable
types already have, so a local copy would avoid nothing and would compose with
nothing, which defeats the purpose of a correspondence library. hex-gfq-mathlib
composes the `GF2n` equivalence with the canonical Conway field through
`RingEquiv.trans`, and that composition is the whole `p = 2` story described in
that library's SPEC.

**Finiteness.** `GF2n` is indexed by its `val` bound directly, and `GF2nPoly`
through its reduced-representative subtype, rather than by transporting a
`Fintype` across the ring equivalence. Both routes give the same cardinality;
the direct one does not depend on the generic side's own finiteness argument.
The resulting `Fintype` instances are computable.

The computational hex-gf2 library stays Mathlib-free. This library owns the
`Fintype`, cardinality, and Mathlib-instance surface promised to downstream
proof libraries, per the rule in `SPEC/design-principles.md` that Mathlib
typeclass instances on an executable type live in the `*-mathlib` companion,
transported along the equivalence so the operations stay the executable ones.

## Reaching Mathlib's own types

`GF2Poly ≃+* FpPoly 2` lands on a Hex type, not a Mathlib one. Composing it
with `FpPoly p ≃+* Polynomial (ZMod p)` gives `GF2Poly ≃+* Polynomial (ZMod 2)`,
which is where a Mathlib user starts. That second equivalence is not yet in a
library this one can depend on.

## External comparators

No external comparator is required.

**Justification:** `proof-only-layer` per
`SPEC/benchmarking.md §"Comparator naming"`. This library contains no
executable algorithm of its own: it states correspondences between
representations that hex-gf2 and hex-gfq-field implement, and their performance
is measured in those libraries. There is nothing here for an external tool to
race against.
