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
The existing [manual chapter](../HexManual/Chapters/HexRCF.lean) includes a
focused [subsection](../HexManual/Chapters/HexRCF/ClosedCoefficients.lean) that
runs all three examples and explains the coefficient and divisor behavior.

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

The [included-subsection record](data/hexrcf-maximal-coefficients/followup/context.json)
binds nine source files and the subsequent layout validation at `573922ae85`.
The parent chapter has 2,992 lines and its included subsection has 44;
both satisfy the 3,000-line source cap. The full 14,298-job render passes
in 2m52.565s at 2.2 GiB peak. The separate browser capture passes in 11.512s
at 6.4 GiB peak, with all eight relocated captures opened and zero local
overflow. Its dependency, admission, copyright and line-count checks pass.
The retained earlier render failure identifies an invalid subsection placement;
the final include follows the parent section's blocks as Verso requires.
Production frontend code and the audited conformance proof bodies are unchanged
by this documentation split. The earlier record and images remain intact.

The [integration record](data/hexrcf-maximal-coefficients/integration/context.json)
binds 38 selected files, nine logs and the active memory-limit snapshot. Its
source at `05180c1e6c` integrates owner main `7244ae8f3c` and reviewed parent
`4bc1dd7bb0`; it checks the assembled original goal and a fresh real witness
under maximal abstraction. The negative-conjugate control now retains the
whole negative coefficient and rejects the wrong valuation. A separate
positive-coefficient control preserves rejection of a changed polynomial.
The foreign-coefficient and both original-guard count controls remain, each
checking the expected diagnostic and state restoration.

That focused 11,205-job selection passes in 13m15.053s at 9.1 GiB peak;
the assembled source module takes 422 seconds and its fresh consumer 7.2 seconds.
Source `0a041add65` preserves the existing target order while adding the three
new default roots. Its broader 14,350-job selection passes in 13m14.764s at
9.6 GiB peak, including the optional umbrella, actual assembled proof,
ordinary-real models, source preparation, caller-constant compatibility,
handler tests and full manual. These selections have different rebuild scopes;
their similar command times are not a performance comparison. Existing checked
modules may be replayed from the cache in the broader selection.
The integrated metadata checks cover 662 import cones and 1,563 modules;
both eleven-test checker suites pass. The retained failed joint Python test
invocation concerns its import path; the documented discovery invocation passes.
The maximal-coefficient manual sources are byte-identical to their separately
inspected layout source. Local integration with a reviewed parent is not a
claim that the parent PR has landed or that the general backend is complete.

The [landed-main record](data/hexrcf-maximal-coefficients/landed-main/context.json)
subsequently verifies the actual parent squash `e2cffe51a4` and its successful
exact-head CI, with the source branch retained. Source `795fab86b3` also
consumes the merged public graph-reader export (`3c0e1df6cf`) and shared
finite-support implementation (`768d2768a3`). Its 14,340-job selection passes
in 17m33.791s at 13.4 GiB aggregate peak with zero swap. The actual assembled
source module takes 424 seconds and its fresh consumer 5.4 seconds in that
selection. The optional-umbrella public graph-reader regression now passes;
the earlier private-import diagnostic is no longer an unresolved export gate.
The metadata audit covers 666 import cones and 1,567 modules, and both
eleven-test checker suites pass. The record binds 45 files, seven logs and four
validation artifacts. It preserves the earlier local-integration records and
does not turn their observations into controlled timing comparisons.

A [separate compiled probe](data/hexrcf-maximal-coefficients/missing-records/context.json)
constructs `NativeOperations.extend` with empty packing, stored-sign and inverse
inventories. Using the existing strict scalar codec and the same valid literal
root/cell packet, `CellOperations.accept?` returns `some ()`. The build-only
probe completes 11,112 selected jobs in 22.877s at 3.3 GiB peak with zero swap.
It requests no ordinary-kernel acceptance proof. This confirms the documented
compiled native fallback; it is not evidence of mathematical unsoundness or a
strict checker. The general frozen frontend still needs the owner's strict
inventory-replay or coverage boundary to reject every missing reached record.

## Registered equality witnesses and compatibility

Maximal abstraction can change handler eligibility. A bare supported generator
retains the original single-coordinate handler; arithmetic such as `2 * sqrt 2`
uses the common-field handler. The latter reuses one selected field when there
is only one generator. The `ReplayModes`, `TotalAlgebraicProofs`, `CarrierModes`
and registered-constant modules all rebuild successfully, including their
existing option and diagnostic assertions. No source schema is changed back to
leaf abstraction to preserve an optimization.

For a registered existential, coefficient order need not put the required
witness first. In `∃ x, x < c + 1 ∧ x = c`, the first maximal coefficient is
`c + 1`. Finite proof construction now prefers the value directly stated by
`x = c` or `c = x` in a conjunction. It never searches below a binder or through
disjunction, implication or negation. Loose bound variables and metavariables
are excluded. Metadata on the existential predicate is stripped before matching
its lambda; other shapes keep the existing witness fallback. The selected
witness remains a proof-search proposal checked against the original goal.
This does not establish total named-constant witness search.

The [witness validation record](data/hexrcf-maximal-coefficients/witnesses/context.json)
binds fifty source files, seventeen logs and eleven artifacts. The actual
three algebraic theorem types now have assertions for their whole ordered
coefficient inventory. The exact zero-product/zero-divisor example in the manual
also has a direct `rcf` refusal test. The negative-source control checks that its
formula agrees with the positive source before testing the changed valuation.
The registered square-bound theorem is named and included in the fresh body
audit. Both reordered equality orientations and the metadata case assert that
the first coordinate differs from the witness and require the caller's
registration dependency. A nonlinear aliased existential also requires that
dependency. The fresh importing module checks all eight named bodies and their
combined transitive axiom closure, requiring exactly the standard three axioms.

| Completed selection | Source | Observation |
| --- | --- | --- |
| Affected routing and option regressions | `9a78ec535b` | 11,137 jobs; 2m46.137s; 4.5 GiB peak |
| Whole inventory, zero refusal and six proof bodies | `dc7c722689` | 11,138 jobs; 27.447s; 1.6 GiB peak |
| Full integration and unchanged-formula control | `dc7c722689` | 14,347 jobs; 8m20.196s; 9.2 GiB peak |
| Metadata, aliases and eight proof bodies | `9483d01c03` | 11,138 jobs; 37.457s; 1.6 GiB peak |
| Explicit alias-provider dependency | `c6ea8386fd` | 11,138 jobs; 32.364s; 1.4 GiB peak |
| Final manual render | `9483d01c03` | 14,300 jobs; 3m37.019s; 3.7 GiB peak |
| Final inspected desktop/narrow captures | `9483d01c03` | 11.553s; 8.2 GiB peak |

These are incremental validation scopes, not matched comparisons. All use the
same aggregate 32 GiB/no-swap limit and serial own-build discipline. Metadata
checks pass on the final production source; the later change adds only the
alias dependency assertion. Earlier failed inventory assertions are retained
and excluded from successful selections. The final manual source is unchanged
by that assertion; all eight captures were opened and the changed targets have
zero local overflow. Earlier evidence records and captures remain intact.
