# Ordered rational-function computations

`HexOrderedFn` supplies exact rational bounds, Horner enclosure and per-query
total refinement over the existing canonical `Hex.RationalFn` arithmetic. It
imports neither Mathlib nor an interval library. The full contract is in
[hex-ordered-fn](../SPEC/Libraries/hex-ordered-fn.md).

`Oracle.Approximation` contains only computational coefficient and constant
providers. `Approximation.ofConstant` starts over rational coefficients with
exact singleton bounds. `Oracle.ApproximationWidth` states their
requested-width guarantees separately; the companion's `ApproximationCorrect`
states containment for the same providers, embedding, subject and requests.

`Oracle.Bounds` provides singleton bounds (including exact dyadic conversion),
negation, addition, four-endpoint multiplication, intersection and conditional
four-endpoint division. `sign?` requires strict separation; `exactSign?` also
accepts the exact singleton zero. Bounds merely touching zero do not determine
a nonzero sign. Conditional bound division is separate from total field
division.

`Real.enclose` uses an array Horner loop. Every coefficient and the new
constant receive the same requested width. `Real.attempt` signs a canonical
fraction's numerator and denominator bounds; formal zero returns immediately.
`Real.approxAttempt` tests both denominator separation and quotient width.

`Real.sign` and `Real.approx` execute these trials from precision zero under
an erased accessibility proof. Positive requests to `approx` have separate
width and containment theorems; nonpositive requests execute the same search
with requested width one. Containment therefore holds for every returned
bound. `Real.sign?` is a separate finite consumer that checks denominator
regularity and can recognize an exact-zero numerator. It is never registered
as a field operation.

The generic `firstSome` search supports any result type. Its proofs include
the first-success characterization, equations for success and refinement,
eventual-success accessibility, and `acc_of_success` for one checked finite
success. A witness at precision N proves termination; the executable still
tries all precisions from its requested start and may stop before N.
Termination evidence alone establishes no semantic validity.

Build the computational regression tests with:

```sh
lake build HexOrderedFn HexOrderedFnTests +HexOrderedFn.Conformance
```

Tests include negative denominator bounds, poles, non-dyadic rationals,
zero-touching bounds, joint refinement, finite exhaustion, and compiled total
sign and bound searches with earlier failed trials. Kernel proofs check the
finite witnesses. These are regression tests, not Phase-4 measurements.

The library remains at phase 0: the complete Phase-1 API is not present.
Universal progress from shrinking bounds and relative transcendence,
ordered-field registration, infinitesimal extensions, provider/context
certificate boundaries, Z3/exact conformance and performance evidence remain
outstanding under [#10376](https://github.com/kim-em/hex-dev/issues/10376).
Per-query finite witnesses do not register a transcendental field.
