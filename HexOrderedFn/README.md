# Ordered rational-function computations

`HexOrderedFn` supplies infinitesimal orders, exact rational bounds, Horner
enclosure and per-query total refinement over the existing canonical `Hex.RationalFn` arithmetic. It
imports neither Mathlib nor an interval library. The full contract is in
[hex-ordered-fn](../SPEC/Libraries/hex-ordered-fn.md).

`Infinitesimal.sign` takes a predecessor sign and scans the first nonzero
numerator and denominator coefficients. `Infinitesimal.compare` compares by
the sign of subtraction. `open scoped Hex.OrderedFn.Infinitesimal` enables
`<` and `≤` on `RationalFn K`, using the predecessor order. No global order
is imposed on the rational-function carrier. The same construction works
successively on `RationalFn (RationalFn Rat)` and further levels. The real
registration API, still outstanding, uses a distinct provider-indexed wrapper
so an infinitesimal scope does not also order its real predecessor infinitesimally.

```lean
import HexOrderedFn
open Hex Hex.OrderedFn
open scoped Hex.OrderedFn.Infinitesimal

def epsilon : RationalFn Rat := RationalFn.X
def delta : RationalFn (RationalFn Rat) := RationalFn.X
#eval decide (delta < RationalFn.C (epsilon ^ 3)) -- true
#eval Infinitesimal.sign orderSign (1 / (epsilon - 1)) -- -1
```

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
sign and bound searches with earlier failed trials. Kernel proofs check the finite witnesses. Infinitesimal fixtures cover negative
valuations, negative denominators, cancellation and three successive levels;
`scripts/oracle/ordered_fn_z3.py` checks them with pinned Z3 RCF and exact
rational specialization. `hexorderedfn_bench` measures sign scans, comparisons,
degree, coefficient height and tower depth without importing Mathlib. Run it
with `scripts/bench/ordered_fn_measure.py --output DIR`. The companion's
mathematical proofs are checked by its ordinary-kernel tests.

The library remains at phase 0: the complete Phase-1 API is not present.
Universal progress from shrinking bounds and relative transcendence,
real ordered-field registration, provider/context certificate boundaries,
Liouville integration and complete real-extension conformance/performance evidence remain
outstanding under [#10376](https://github.com/kim-em/hex-dev/issues/10376).
Per-query finite witnesses do not register a transcendental field.
