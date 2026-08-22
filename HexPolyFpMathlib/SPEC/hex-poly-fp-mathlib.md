# hex-poly-fp-mathlib (depends on hex-poly-fp + hex-poly-mathlib + hex-mod-arith-mathlib + Mathlib)

The crossing point between the executable prime-field polynomial tower and
Mathlib's own polynomial type.

**Contents:**

- `fpPolyToPolynomial : FpPoly p → Polynomial (ZMod p)` and
  `polynomialToFpPoly` the other way.
- `fpPolyEquiv : FpPoly p ≃+* Polynomial (ZMod p)`, the ring equivalence they
  assemble into.
- `toMathlibPolynomial`, the forward map named for use in statements, with its
  coefficient, monicity, and `simp` lemmas.

Everything below this library is Hex's own tower: `DensePoly` over `ZMod64`,
reached through hex-poly-mathlib and hex-mod-arith-mathlib. Everything a
Mathlib user starts from is on the far side of `fpPolyEquiv`.

## Ownership

Any library relating an `FpPoly`-backed construction to Mathlib depends on this
one: hex-gf2-mathlib composes the equivalence with the packed correspondence to
state `GF2Poly ≃+* Polynomial (ZMod 2)`, and the finite-field construction
libraries need it to speak about their moduli in Mathlib's terms. None of them
should have to depend on a factoring library to reach Mathlib.

hex-berlekamp-mathlib re-exports the names, so call sites spelling them
`HexBerlekampMathlib.fpPolyEquiv` resolve unchanged.

The equivalence needs only `ZMod64.Bounds p`, not primality: `FpPoly p` is a
ring for any admissible modulus, and so is `Polynomial (ZMod p)`. Lemmas that do
need `p` prime, such as the coprimality transports, say so in their own
hypotheses.

The dependency on hex-poly-mathlib is narrow and worth naming, since it is not
the obvious one: the generic `DensePoly R ≃+* Polynomial R` cannot be reused
here, because `ZMod64` deliberately carries no Mathlib `Semiring` instance. The
edge exists for the list helper `list_getD_map_range_zero`, which the inverse
map's coefficient reasoning uses.

## What belongs here, and what does not

This library states the correspondence and the lemmas that follow from it
alone. A lemma that mentions Berlekamp's `basisSize`, `isUnitPolynomial`, or
Rabin's test belongs in hex-berlekamp-mathlib even when its conclusion is about
`toMathlibPolynomial`, because it is a fact about the factoring algorithm rather
than about the representation.

## External comparators

No external comparator is required.

**Justification:** `correspondence-only-layer` per
`SPEC/benchmarking.md §"Comparator naming"`. The library introduces no
arithmetic algorithm; it transports values between two representations. The
computational performance owner is hex-poly-fp, which implements and measures
the executable side of the correspondence; the other side is Mathlib's own
`Polynomial`.
