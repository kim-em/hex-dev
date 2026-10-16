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

## Validation evidence

The [context record](data/hexrcf-maximal-coefficients/context.json) binds eight
selected source files, nineteen raw compressed logs and twenty-two artifacts.
Its validation groups identify the source commit of each completed selection;
older failures and narrower checks are retained separately. The broad
compatibility selection includes rational/algebraic tactic conformance,
registered/named/mixed/coarse constants and native source preparation. The
initial squared-bound failure is retained and excluded from successful checks.

| Selection | Source | Completed observation |
| --- | --- | --- |
| Corrected compatibility | `45abf28d48` | 11,143 jobs; 3m1.684s; 12.2 GiB peak |
| Actual tactic proofs and fresh body audit | `ba113787c4` | 11,135 jobs; 2m0.177s; 2.3 GiB peak |
| Full manual and fresh proof audit | `febb5f0410` | 14,299 jobs; 12m22.220s; 18.9 GiB peak |
| Corrected full render | `8469a5a700` | 14,297 jobs; 2m50.730s; 2.3 GiB peak |
| Corrected desktop/narrow capture | `8469a5a700` | 11.220s; 5.1 GiB peak |

The actual three-example proof module takes 12 seconds in the retained
proof selection, including its dependency checks; the fresh importing body
audit takes 8.8 seconds. These are module observations with cached imports,
not isolated timings of each tactic invocation. Broader command times include
other selected rebuilds. All completed Lean, Lake and browser runs use the aggregate 32 GiB cap,
zero swap, two Lean threads and one own build invocation across worktrees.
The retained active-unit snapshot proves the limit; its sampled usage is not
the completed peak. Systemd reports aggregate cgroup memory, including charged
file cache. These host-specific incremental observations are not controlled
comparisons or scaling measurements.

The first narrow capture exposed 96 pixels of local code overflow. Its source,
failed capture and metadata remain under
[`overflow-1`](data/hexrcf-maximal-coefficients/overflow-1/overflow.json).
The corrected examples use ordinary square-root notation and preserve the same
Lean expressions. All eight final captures were opened and inspected. Their
[inspection metadata](data/hexrcf-maximal-coefficients/maximal-coefficients-inspection.json)
reports zero local overflow for the changed targets; the whole book and older
code blocks are outside that layout claim.
