# hex-real-algebraic-mathlib

The companion shares the
[ordered real algebraic number specification](../../SPEC/Libraries/hex-real-algebraic.md)
with the computational library. It proves closure, arithmetic and order
correspondence, root completeness and multiplicities, rounding, approximation,
rational recognition, and real-closedness. Its semantic maps and polynomial
views are noncomputable; its field and order dictionaries explicitly retain
the computational library's executable data. The proof-only `Laws` witness
supplies the conditional core dictionaries without introducing a new algorithm.

Conformance fixtures and any performance measurements belong to
`HexRealAlgebraic`. This companion has no separate oracle, benchmark, checker,
reifier, or proof-generation interface. Its regression modules check theorems,
axiom dependencies, and dictionary coherence during compilation.
`lake build HexRealAlgebraicMathlibTests` builds those ordinary-kernel guards
from `HexRealAlgebraicMathlib/Tests.lean`. Phase eligibility follows the core's
direct dependencies and attestation in `libraries.yml`; it does not require
a separate timing report for this theorem-only companion.

## Headline correctness theorem

`Hex.RealAlgebraicPoly.roots_spec` in `Roots.lean` states the end-to-end
postcondition of the implemented real polynomial root driver. Its clauses are:

- The universal root set is returned exactly for the zero polynomial.
- Semantic membership is equivalent to polynomial evaluation being zero for
  every real value, including values not supplied as executable inputs.
- Executable membership agrees with evaluation at a real algebraic number.
- The finite root view is strictly increasing, hence has no duplicate values.
- Each finite entry carries its exact positive polynomial root multiplicity.

The existing completeness, zero-polynomial, sorting, membership and multiplicity
theorems compose into this result. `HexRealAlgebraicMathlibTests` checks its
ordinary-kernel axiom dependencies. Scalar arithmetic/order laws and dictionary
coherence, implemented `compare_eq`, checked constructors, rational recognition,
rounding, approximation, square roots, Repr and integer-root correspondence
remain independently required public contracts: the root driver does not
expose those operations. Their named correspondence theorems and axiom guards
remain part of the readiness audit. The excluded forward comparison extension
below is not included in this headline or the shipped attestation.

`RealAlgebraicNumber.ofRoot?_eq` identifies early rejection using the stored
refined isolation with canonical exactification followed by the reality check.
Its ordinary-kernel guard protects the complete equality, including nonreal
inputs; the root completeness and multiplicity results reuse that equality.

This theorem builds in the ordinary companion target. `libraries.yml` records
Phase 4 after the core, with ordinary-kernel correctness and axiom checks in
the [readiness audit](../../reports/real-closure-prerequisites.md).

## Array and comparison correspondence

This section specifies the forward comparison-strategy extension owned by
HexNumberField and HexNumberFieldTower. These new array and transport
obligations are unimplemented and excluded from the shipped surface's current
phase attestations, as specified at the end of the shared exact-comparison
contract. The implemented `compare_eq` and polynomial-root correspondence
remain required and are proved in the modules named above.


The [exact comparison contract](../../SPEC/Libraries/hex-real-algebraic.md#exact-comparison-strategies)
adds `sort_perm` and `sort_sorted`, identifying the array sort with a permutation
in nondecreasing `realCompare` order. On canonical values, equality of comparison
keys is equality of values, so no separate stability theorem is needed for an
untagged array. `min?_eq` and `max?_eq` identify Lean's array extrema with folds
of the reference scalar operations, including empty arrays. `compareArray_eq`
identifies the existing array `Ord` with lexicographic `realCompare` after
projecting to canonical algebraic numbers.

`compareIndex_eq` requires indices into a certified strictly increasing array
of distinct real values. Use the existing `realAlgebraicRoots_sorted` and
`realAlgebraicRoots_nodup` for the exact-sorted root view. To reuse raw
`algebraicRoots` order without sorting, require that all real entries share
one minimal polynomial and use the new number-field `rootLe_real` bridge.
Do not infer value order from `algebraicRoots_sorted` across different factors;
that theorem concerns stored centre keys. The initial exact sort for a general
reducible polynomial is part of the computational cost.

The number-field companion owns `realCompare_eq_exact` and all point, lazy,
and fixed-field correspondence. This companion transports those equations
through the real subtype and retains its existing `compare_eq`, order laws,
and executable dictionaries. When implemented, the new array obligations will need conformance and
performance evidence in `HexRealAlgebraic`; no proof-generation API is added.

Phase attestation is recorded in `libraries.yml`; the readiness audit gives
the conformance/correctness evidence and remaining requirements.
