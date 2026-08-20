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

## Why this is its own library

The equivalence originally lived in hex-berlekamp-mathlib, because factoring
over `F_p` was its first consumer. It is not specific to factoring. Any library
that relates an `FpPoly`-backed construction to Mathlib needs it:
hex-gf2-mathlib composes it with the packed correspondence to state
`GF2Poly ≃+* Polynomial (ZMod 2)`, and the finite-field construction libraries
need it to speak about their moduli in Mathlib's terms.

Leaving it in a factoring library meant those consumers had to depend on
factoring to reach Mathlib, which is both a false dependency and an awkward one:
hex-berlekamp-mathlib is well behind them in the phase order, so depending on it
would have coupled a mature library to an immature one.

hex-berlekamp-mathlib re-exports the names it moved, so call sites that spelled
them `HexBerlekampMathlib.fpPolyEquiv` continue to work.

## What belongs here, and what does not

This library states the correspondence and the lemmas that follow from it
alone. A lemma that mentions Berlekamp's `basisSize`, `isUnitPolynomial`, or
Rabin's test belongs in hex-berlekamp-mathlib even when its conclusion is about
`toMathlibPolynomial`, because it is a fact about the factoring algorithm rather
than about the representation.

## External comparators

No external comparator is required.

**Justification:** `proof-only-layer` per
`SPEC/benchmarking.md §"Comparator naming"`. The library introduces no
arithmetic algorithm; it transports values between two representations whose
performance is measured in hex-poly-fp and in Mathlib respectively.
