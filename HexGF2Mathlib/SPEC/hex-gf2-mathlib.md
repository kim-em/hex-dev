# hex-gf2-mathlib (depends on hex-gf2 + hex-poly-fp + hex-gfq-field + Mathlib)

## Correspondence-only classification

This library is a `correspondence-only-layer`.

Computational conformance owners: `HexGF2`, `HexGFqField`
Computational performance owners: `HexGF2`, `HexGFqField`

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

**Algebraic structure.** `CommRing GF2Poly`, `EuclideanDomain GF2Poly`, `Field
(GF2n n irr hn hn64 hirr)`, and, for a nonconstant modulus, `Field (GF2nPoly f
hirr)` are built from laws hex-gf2 already proves. The `GF2Poly` multiplication,
division, and remainder stay the executable packed operations. The primitive
operations accepted by the field constructor stay executable too; for `GF2n`,
the default subtraction and division also agree definitionally with the packed
API. Thus both `p * q = GF2Poly.mul p q` and `a * b = GF2n.mul a b` close by
`rfl`. The remaining derived hierarchy operations use Mathlib's constructor
defaults. Building the structures by transport along the ring equivalences
instead would attach the right laws to the wrong operations.

The Euclidean relation measures zero at `0` and a nonzero polynomial at one
greater than its degree. The remainder-decrease proof is therefore exactly
`GF2Poly.mod_degree_lt`, including the zero-remainder case, while multiplication
of nonzero polynomials cannot lower the measure. The `GCDMonoid` instance is
built directly from `GF2Poly.gcd_dvd_left`, `gcd_dvd_right`, and `dvd_gcd`, so
`GCDMonoid.gcd p q = GF2Poly.gcd p q` holds definitionally. Mathlib's Bezout,
principal-ideal, and unique-factorization interfaces are consequently available
without replacing the packed arithmetic. The separately recursive
`EuclideanDomain.gcd` is proved equal to `GF2Poly.gcd` by
`GF2Poly.euclidean_gcd_eq_packed`, using antisymmetry of divisibility over
`F₂[x]`, so Mathlib's explicit Euclidean Bezout theorem has the same gcd value.
The `GCDMonoid` class also requires an `lcm`; that projection is supplied
noncomputably by Mathlib's constructor and is not a packed executable API.

The field instance takes `Fact (0 < f.degree)`. The degree hypothesis is not
redundant: `GF2Poly.Irreducible` admits the constant `1`, and `GF2nPoly 1 _` is
the trivial ring where `0 = 1`, so neither `zero_ne_one` nor characteristic two
holds for every modulus the type accepts. hex-gfq-field avoids the same trap by
carrying the degree bound as a type parameter.

The computational hex-gf2 library stays Mathlib-free.

## Reaching Mathlib's own types

`GF2Poly ≃+* FpPoly 2` lands on a Hex type, not a Mathlib one. `equivPolynomial`
composes it with `FpPoly p ≃+* Polynomial (ZMod p)` from hex-poly-fp-mathlib to
give `GF2Poly ≃+* Polynomial (ZMod 2)`, which is where a Mathlib user starts. It
is `noncomputable`, since Mathlib's polynomial multiplication is; the packed
side stays executable.

## External comparators

No external comparator is required.

**Justification:** `correspondence-only-layer` per
`SPEC/benchmarking.md §"Comparator naming"`. This library introduces no new
arithmetic algorithm: it states correspondences between representations that
hex-gf2 and hex-gfq-field implement, and those two are the computational
performance owners, where the arithmetic is measured. The encoding and decoding
functions it does define exist to state those correspondences, not as a
computational surface anyone races.
