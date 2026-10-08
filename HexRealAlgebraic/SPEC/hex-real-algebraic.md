# hex-real-algebraic

The computational library and its Mathlib companion share the
[ordered real algebraic number specification](../../SPEC/Libraries/hex-real-algebraic.md).
All arithmetic, comparison, root finding, rounding, approximation, rational
recognition, and checked construction belong to this Mathlib-free library.
The [readiness audit](../../reports/real-closure-prerequisites.md) records the
implemented surface and its companion proofs. `libraries.yml` records phase
attestation through Phase 4; the
[performance report](../../reports/hex-real-algebraic-performance.md) records
coverage decisions, source-scoped observations and supported limits. The forward comparison-strategy
extension is excluded from the implemented surface, as the shared SPEC states.

## Headline correctness theorem

`Hex.RealAlgebraicPoly.roots_spec` is the bridge headline for the implemented
root driver. It combines universal roots exactly for zero, real-root
completeness, executable membership, strict ordering and positive exact
multiplicities. The
[companion contract](../../HexRealAlgebraicMathlib/SPEC/hex-real-algebraic-mathlib.md#headline-correctness-theorem)
also identifies the independently required scalar and representation contracts,
including the implemented comparison API. The forward comparison extension
remains excluded; the separate compiled evidence is recorded in the performance
report.

## Shared comparison and complex norm operations

Real order inherits the stored-interval and bounded adaptive refinement paths
of `AlgebraicNumber.realCompare`; the exact comparison theorem is unchanged.
The square-root API shares the optimized complex square-root selector while
retaining negative-input rejection and its nonnegative real result.
Lazy-root conversion rejects nonreal refined isolations before canonical
exactification. `ofRoot?_eq` proves equality with the original conversion;
real-root filtering retains exactly the same canonical values and multiplicities.
`AlgebraicNumber.normSq` and `AlgebraicNumber.abs` belong here and return
`RealAlgebraicNumber`, as do `re` and `im`. Their companion identifies them
with the complex squared norm and norm and proves nonnegativity, zero
characterizations, conjugation invariance, multiplicativity, and the square
identity. Computational number fields never import their real subtype.

Phase attestation is recorded in `libraries.yml`; the readiness audit gives
the conformance/correctness evidence and remaining requirements.
