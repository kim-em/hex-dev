# hex-real-algebraic

The computational library and its Mathlib companion share the
[ordered real algebraic number specification](../../SPEC/Libraries/hex-real-algebraic.md).
All arithmetic, comparison, root finding, rounding, approximation, rational
recognition, and checked construction belong to this Mathlib-free library.
The [readiness audit](../../reports/real-closure-prerequisites.md) records the
implemented surface and its companion proofs. `libraries.yml` records phase
attestation; the [performance report](../../reports/hex-real-algebraic-performance.md)
lists the remaining Phase-4 requirements. The forward comparison-strategy
extension is excluded from the implemented surface, as the shared SPEC states.

## Shared comparison and complex norm operations

Real order inherits the stored-interval and bounded adaptive refinement paths
of `AlgebraicNumber.realCompare`; the exact comparison theorem is unchanged.
The square-root API shares the optimized complex square-root selector while
retaining negative-input rejection and its nonnegative real result.
`AlgebraicNumber.normSq` and `AlgebraicNumber.abs` belong here and return
`RealAlgebraicNumber`, as do `re` and `im`. Their companion identifies them
with the complex squared norm and norm and proves nonnegativity, zero
characterizations, conjugation invariance, multiplicativity, and the square
identity. Computational number fields never import their real subtype.

The library records Phase 3 in `libraries.yml`; the readiness audit gives the
conformance/correctness evidence and remaining Phase-4 requirements.
