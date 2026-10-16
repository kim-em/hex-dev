# Maximal closed coefficients

The [source frontend](../adapters/HexRCF/RealCoefficients/Reify.lean)
abstracts each maximal closed real expression containing a supported algebraic
or registered subject. Thus `sqrt 2 + sqrt 3`, its square, its negative and
a closed quotient each occupy one coefficient coordinate. Repeated identical
expressions share a coordinate; a separately occurring constituent retains its
own coordinate in source traversal order. Purely rational arithmetic stays in
the shared integer polynomial schema.

Original division guards are collected before this abstraction or any
normalization. Variable-bearing division becomes multiplication by a closed
inverse; a wholly closed quotient stays whole. In particular, multiplication
by zero does not hide the divisor in `0 * (1 / (sqrt 2 - sqrt 2))`.
The pending source equivalence still describes Lean's total division;
coefficient admission separately refuses its original zero divisor.

The [source regressions](../conformance/HexRCF/MaximalCoefficients.lean)
check the complete ordered coefficient and divisor inventories, including
sums, repetition, a separately used constituent, rational multiplication,
negation, natural powers, inverses, quotients, zero multiplication, `pi - 4`
and arithmetic containing an opaque registered subject. Each schema's
original-goal equivalence is checked in the ordinary kernel. An importing
module requires the final completion declaration.

The [actual tactic proofs](../conformance/HexRCF/MaximalCoefficientsConformance.lean)
establish positivity for a closed sum and its square, and an existential
negative witness. Their dependency checks require the real-coefficient
universal or existential soundness theorem. A separate
[fresh kernel consumer](../conformance/HexRCF/MaximalCoefficientsKernel.lean)
rechecks the theorem bodies and their transitive axiom closure, requiring
exactly `propext`, `Classical.choice` and `Quot.sound`.
The existing [manual chapter](../HexManual/Chapters/HexRCF.lean) runs all three
examples and explains the coefficient and divisor behavior.

The supplied-bound proof constructor normalizes only `mkRat` and division
before nonlinear arithmetic. This preserves a supplied bound on a square:
unrestricted simplification can replace it with an absolute-value bound that
the subsequent arithmetic step cannot use. The existing registered-constant
regression exercises this case. This change does not provide an approximation
procedure or assume a sign for an unresolved divisor.

This frontend change does not complete the general native backend. Computed
proposals still require literal source authentication and frozen histories;
general original-source certificate acceptance, strict missing-record
rejection, realization and the remaining completeness/stress obligations are
separate requirements of #10358. The fixed-field proof examples establish
neither those results nor a general performance improvement.
