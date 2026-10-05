# Ordered-function proof and API review

The review covers the production modules of `HexOrderedFn` and
`HexOrderedFnMathlib`, their public umbrellas, and their existing tests and
conformance interfaces. It supports the pair's Phase-5 proof-completion checks
and supplies API improvements for Phase 6. It does not attest Phase 6 or Phase 7
completion. The retained computational baseline is in
[the performance report](hex-ordered-fn-performance.md).

## Computational declarations

| Module | Definitions and proof boundary reviewed | Result |
| --- | --- | --- |
| [Search](../HexOrderedFn/Search.lean) | `Next`, `acc_of_success`, `next_acc`, the accessible-subtype termination instance, `firstSome` and its first-success/specification/equality lemmas | A finite successful trial suffices; later trials need not stay successful. Accessibility erases and supplies neither a runtime answer nor fuel. Agreement of successful values remains a separate premise. |
| [Oracle](../HexOrderedFn/Oracle.lean) | Closed bounds, singleton/dyadic construction, negation, addition, four-corner multiplication, intersection, separation, inversion/division, finite signs, approximation providers and width witnesses | Endpoint order is structural; containment is semantic. Intersection has endpoint extensionality, an exact success condition and a returned-endpoints characterization. Negation and addition have exact width normalization lemmas. |
| [Real](../HexOrderedFn/Real.lean) | Joint coefficient/argument refinement in Horner evaluation, numerator/denominator enclosure, bounded signs, total attempts/search, positive width normalization and approximation | Bounded `sign?` checks the stored denominator even for formal zero; total `attempt` returns zero immediately for the canonical zero fraction. Totality needs erased progress evidence. `requestWidth_of_nonpos` characterizes the normalization without unfolding it. Original source divisors belong to expression consumers. |
| [Extension](../HexOrderedFn/Extension.lean) | Fixed `Registration`, canonical-fraction wrapper, native field dictionary, coefficient/indeterminate constructors, sign/comparison/approximation, provider transport and next-level approximation | Termination alone supplies no ordered-field laws. `val_C` and `val_X` expose storage independently of proofs. Transport preserves the canonical fraction literally; preserving order requires the companion's same-subject hypotheses. |
| [Infinitesimal](../HexOrderedFn/Infinitesimal.lean) | Lowest nonzero coefficient scan, canonical fraction sign, comparison and scoped decidable relations | Both numerator and denominator affect sign. The four scoped instances have short explicit names. A native field dictionary and decidable relations are separate from Mathlib ordered-field laws. |

## Semantic declarations

| Module | Definitions and proof boundary reviewed | Result |
| --- | --- | --- |
| [Oracle](../HexOrderedFnMathlib/Oracle.lean) | `Contains`, provider correctness, endpoint arithmetic and quotient containment | Four-corner multiplication handles all endpoint signs. Shared containment proves intersection succeeds; its containment law uses the endpoint characterization rather than unfolding the operation. Inversion/division require strict zero separation; finite containment is distinct from a shrinking-width guarantee. |
| [Evaluation](../HexOrderedFnMathlib/Evaluation.lean) | Polynomial evaluation, relative transcendence, denominator nonvanishing, rational-function evaluation, injective homomorphism and constructor equations | Transcendence is over the entire predecessor field, not merely over the rationals. The field interpretation uses that hypothesis to justify nonzero canonical denominators. |
| [Real](../HexOrderedFnMathlib/Real.lean) | Horner/enclosure soundness, finite attempt and bounded sign soundness, total sign and approximation specifications | Successful-trial soundness uses containment; total-search specifications consume progress. Stored denominator guards do not recover source-expression guards erased by cancellation. |
| [Convergence](../HexOrderedFnMathlib/Convergence.lean) | Endpoint convergence, sums/products, actual Horner convergence, simultaneous refinement and quotient convergence away from zero | Coefficients and argument narrow together; product estimates retain the cross term. The quotient result uses denominator separation rather than total real division at zero. |
| [Progress](../HexOrderedFnMathlib/Progress.lean) | Eventual sign/approximation success and accessibility witnesses | Containment, positive-request widths and relative transcendence supply total progress. The search laws are reused rather than replaced with an opaque answer. |
| [Extension](../HexOrderedFnMathlib/Extension.lean) | `Valid`, registration, `OrderValid`, field-model equality, evaluation homomorphisms, induced orders, constant embedding, same-subject transport and derived-provider correctness | `Valid.orderValid` carries registration's same witnesses into its order hypothesis. `registration_source` identifies the actual provider. Preserving a pre-existing predecessor order additionally requires a strictly monotone embedding; `Valid` alone does not supply it. |
| [Hahn](../HexOrderedFnMathlib/Hahn.lean) | Coefficient maps, support/order/leading coefficient, order comparison and constant embedding | A strictly monotone coefficient homomorphism preserves and reflects Hahn order. Support statements include zero. |
| [Infinitesimal](../HexOrderedFnMathlib/Infinitesimal.lean) | Trailing-degree scan correspondence, Laurent embedding/injectivity, arbitrary fraction presentation, normalization, sign/order laws, constants/indeterminate, successive embeddings | The interpretation is an ordered Laurent/Hahn field; it is not an ordinary-real embedding or a real-closedness claim. The original denominator's nonvanishing remains explicit for arbitrary presentations. |

Public fields and lemmas have source documentation, including non-obvious private
helpers. The API lint target selects the actual module roots, rather than
declaration namespaces, and checks theorem documentation as well as the default
environment linters. The extensionality laws have source docstrings, so
the lint checks need no declaration exemptions. The production umbrellas do not
import the lint target.

The private production helpers are used by their owning proofs: `accessibleWf`
implements the accessible-subtype recursion; `mul_bounds` proves multiplication
and division containment;
`poly_coeff` and `poly_ne_zero` support the Laurent embedding's support, order
and fraction laws; `sign_poly` proves fraction signs; the lowest-index and
coefficient map lemmas prove coefficient transport. The shared public
`Oracle.cast_sign_neg`/`cast_sign_nonpos` characterize integer signs for both
real and infinitesimal strict/nonstrict order equivalences. The bounded search's `go` is its executed
recursion. Public standalone normalization and transfer lemmas are exported API,
not alternate implementations of the algorithms.

## Verification and remaining phase checks

The default Lake test target includes the API lint module. Existing semantic
tests retain ordinary-kernel axiom guards, and the compiled Liouville integration
exercises registered searches after proof erasure. The native conformance suite
and exact fixture oracles cover finite exhaustion, poles, joint refinement and
successive infinitesimals. The README examples use ordinary public imports;
the manual also demonstrates obtaining a registered linear order directly from
`Valid.orderValid` and using its ordered-ring laws.

Both libraries' production declarations contain no `sorry`, added axioms or
`native_decide`. The full build, existing native conformance, Liouville checks
and exact emitted-fixture oracles supply the Phase-5 checks. Computational
operations and searches use the native Lean implementation.

The [retained regression observations](bench-results/ordered-fn-api-regression/README.md)
compare the last committed benchmark baseline to the API candidate. They cover
all 17 retained native workload families, with 816 completed adjacent arms and
matching result hashes. Final performance acceptance remains distinct from
collecting those observations: whole pinned builds use different Lean versions,
and the retained slower points need their stated interpretation. At review
commit [`484c5405fe`](https://github.com/kim-em/hex-dev/tree/484c5405fe7f7b34e01854510006d80b42856063),
the rebuilt benchmark has SHA-256
`6479b2306cb778b7f34ec681020322212607e518577ecae9912f06e0a1ab0fed`,
identical to the measured candidate. The comparison remains descriptive; it
does not supply a Phase-6 performance acceptance verdict.

Phase 6 still requires completion of its acceptance review, including the
performance decision, no-dead-declarations criterion, documentation and
Mathlib-quality review of each nontrivial declaration. A linter pass or successful
theorem application is not that performance check. The chapter and READMEs
provide documentation, but their existence alone
does not advance Phase 7 ahead of Phase 6. Neither pair is added to the released
manifest by this work.
