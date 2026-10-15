# OrderedFn Theory proof and manual acceptance

`HexOrderedFnTheory` satisfies Phases 6–7 independently of `HexOrderedFn`.
The computational library remains at Phase 5 with its retained regression
findings. This acceptance changes no executable operation, theorem statement,
package requirement or publication eligibility.

## Scope and individual review

The [individual semantic assessment](companion.md) covers every handwritten
nontrivial definition, theorem and named instance in the nine production
modules. The [import and automation assessment](quality.md) records the shared
sign layer, scoped instances, characterizing lemmas and normalization choices.
Those assessments are reused here; a linter or reference count does not replace
them. The two sign lemmas moved to `Sign` without changing their public names or
proofs. The bare `mul_bounds` row in the Oracle assessment refers to
`Hex.OrderedFn.Oracle.Contains.mul_bounds`.

The inventory cross-check accounts for 147 handwritten declarations, including
four named field/order instances. The two projections of `ApproximationCorrect`
are assessed with that structure: coefficient and constant containment bind the
same provider, embedding, subject and positive request. The compiler capture
attributes 292 constants to these modules; its other 143 constants are generated
by Lean, not alternate handwritten implementations.

| Module | Handwritten declarations | Individual assessment |
| --- | ---: | --- |
| `Convergence` | 11 | [Assessment](companion.md#convergence) |
| `Evaluation` | 10 | [Assessment](companion.md#evaluation) |
| `Extension` | 36 | [Assessment](companion.md#extension) |
| `Hahn` | 7 | [Assessment](companion.md#hahn) |
| `Infinitesimal` | 46 | [Assessment](companion.md#infinitesimal) |
| `Oracle` | 17 | [Assessment](companion.md#oracle) |
| `Progress` | 7 | [Assessment](companion.md#progress) |
| `Real` | 11 | [Assessment](companion.md#real) |
| `Sign` | 2 | [Assessment](companion.md#oracle) |

The [source and compiler archive](current/README.md) binds the complete import
capture to `audit/issue-10575-orderedfn-current-input-v7` and
`audit/issue-10575-orderedfn-current-complete-v7`. The owned source files are
byte-identical to the reviewed v4 source after the Mathlib-to-Theory rename;
names, owning modules, declaration kinds and axiom lists also agree. Imported
dependencies and elaborated types are not claimed identical merely from that
source comparison. The present public imports and examples are built separately.

## Public use and encapsulation

The ordinary `import HexOrderedFnTheory` exposes the real extension, generic sign
laws, convergence/evaluation/progress results and Hahn/infinitesimal model through
the existing umbrella. `RealClosureConsumer.Ordered.successive_order` consumes
`X_pos` and `X_lt_pow` through that ordinary import. Tests and the manual exercise
bound intersection, finite sign soundness, real registration, field/order
instances, same-subject provider transport and successive infinitesimals.

All six nontrivial private helpers have actual named proof consumers. Their
uses are recorded below; `lowestIndex_map` reaches the public transport laws
through `lowestCoeff_map`. The one-expression `poly_ne_zero` injectivity bridge
is routine private plumbing under the docstring policy. The other helpers have
explanatory docstrings.

| Private helper | Existing proof consumers |
| --- | --- |
| `Infinitesimal.poly_coeff` | `Infinitesimal.poly_leadingCoeff`, `Infinitesimal.poly_order` |
| `Infinitesimal.poly_ne_zero` | `Infinitesimal.embed_leadingCoeff`, `Infinitesimal.embed_order` |
| `Infinitesimal.sign_poly` | `Infinitesimal.sign_eq`, `Infinitesimal.sign_fraction` |
| `Infinitesimal.lowestIndex_map` | `Infinitesimal.lowestCoeff_map` |
| `Infinitesimal.lowestCoeff_map` | `Infinitesimal.mapHom_sign`, `Infinitesimal.mapHom_sign_of` |
| `Oracle.Contains.mul_bounds` | `Oracle.Contains.div`, `Oracle.Contains.mul` |

The 33 handwritten public declarations below have no retained named users in
the captured environment. Their retention is an API-design judgment about the
individual contracts, not an assertion of production callers. Anonymous examples,
normalization and instance elaboration can leave no named edge; generated
aliases and tests can create edges. The four executable `main` modules omitted
from the single-environment capture and independent experimental Lake projects
remain outside its reference model.

These are promised characterizations of the public representations, embeddings,
orders and provider transport, rather than unused alternative algorithms. Keeping
them prevents consumers from unfolding implementation details. Existing anonymous
examples for registration, positivity and transport are reused. No tests are added
merely to manufacture named uses, and no useful interface is removed on a reference
count alone. This settles the companion's API-retention judgment separately from
the computational library's remaining acceptance.

| Public declaration | Retention judgment |
| --- | --- |
| `Real.RelativeTranscendence.ne_image` | Uses `X-C c` to exclude any already-present coefficient. |
| `Real.evalHom_injective` | Public field-embedding injectivity, available without unfolding the composition. |
| `Real.evalHom_eq_ratFunc` | Restriction to `Type` is documented and follows Mathlib's same-universe evaluator; the underlying embedding remains universe-polymorphic. |
| `Real.registration_source` | Public simp identity exposing that source without registration unfolding. |
| `Real.Extension.coreField_eq` | Verifies the companion induces precisely the computational field dictionary. Its definitional proof is appropriate for implementation identity, rather than an omitted user-facing mathematical theorem. |
| `Real.Extension.sign_neg` | Semantic sign negation obtained from the field homomorphism; no executable replacement. |
| `Real.Extension.sign_mul` | Semantic sign multiplication includes zero. |
| `Real.Extension.sign_eq_zero_iff` | Formal zero iff native total sign is zero, under containment and relative transcendence. |
| `Real.Extension.compare_eq` | Trichotomy handles all three comparison outcomes. |
| `Real.Extension.sign_pos_iff` | Actual registered positivity corresponds to sign one. |
| `Real.Extension.sign_neg_iff` | Actual registered negativity corresponds to sign minus one. |
| `Real.Extension.C_lt` | Explicit strict monotonicity of the predecessor embedding is necessary to preserve an already-chosen predecessor order. |
| `Real.Extension.eval_strictMono` | States monotonicity for the particular proved native linear order. |
| `Real.Extension.OrderValid.strictOrderedRing` | Existential-witness wrapper useful for ordinary callers without exposing a chosen evaluation witness. |
| `Real.Extension.OrderValid.orderedRing` | Corresponding core dictionary wrapper; no new computational instance. |
| `Real.Extension.transport_lt` | Both providers must be checked against the same embedding and subject; arbitrary re-registration cannot imply preservation. |
| `Real.Extension.sign_transport` | Same-subject two-provider correctness preserves the sign. |
| `Real.Valid.orderValid` | Reuses registration's semantic witnesses; does not incorrectly claim the predecessor embedding preserves a pre-existing order. |
| `Hahn.map_support` | Field homomorphism injectivity preserves zero/nonzero coefficients and hence the support, including zero series. |
| `Hahn.map_leadingCoeff` | Handles zero separately and transports the nonzero leading coefficient at the preserved exponent. |
| `Hahn.map_le` | Uses strict comparison and homomorphism injectivity to include equality. |
| `Infinitesimal.embed_leadingCoeff` | Fraction leading coefficient is the quotient of trailing coefficients; stored denominator nonzero justifies cancellation. |
| `Infinitesimal.embed_order` | Nonzero fraction order is the difference of numerator/denominator lowest indices. Explicit nonzero premise is essential. |
| `Infinitesimal.sign_normalize` | Exposes normalization/cancellation invariance through the actual representation theorem. |
| `Infinitesimal.sign_mul` | Semantic embedding proves native sign multiplication. |
| `Infinitesimal.compare_eq` | All native comparison outcomes agree with the Hahn order. |
| `Infinitesimal.towerEmbed_lt` | Preserves and reflects the two-level order using both existing correspondence laws. |
| `Infinitesimal.towerEmbed_C` | Public constant characterization at the second level. |
| `Infinitesimal.orderedRing` | Corresponding grind ordered-ring dictionary, separate from the Mathlib class. |
| `Oracle.Contains.ofDyadic` | Exact conversion containment; public dyadic input API. |
| `Oracle.Contains.inter_isSome` | A common subject implies nonempty overlap by maximum/minimum inequalities. Useful producer-success law. |
| `Oracle.Contains.inter` | Arbitrary successful overlap retains common subjects via the public endpoint characterization. |
| `Real.sign?_sound` | Induction over the executed finite recursion; preserves denominator regularity and sign for any accepted finite output. |

## Semantic hypotheses and field construction

Containment proves arbitrary successful real trials sound, including finite
queries at algebraic subjects. Width convergence and transcendence over the
entire predecessor field separately prove progress of the actual searches.
`sign_of_attempt` identifies the total result from finite checked success without
kernel reduction of unbounded refinement. A finite comparison at a dependent
subject does not construct a transcendental field.

`RelativeTranscendence.preserves_nonzero` supplies the localization evidence for
`Real.evalHom`; `eval_den_ne_zero` rules out poles of canonical denominators.
`Extension.fieldModel` transfers existing rational-function field laws, while
`Extension.field` retains native arithmetic in its data fields.
`Extension.coreField_eq` proves identity with the computational dictionary.
The real order retains the core decisions, with evaluation witnesses used only
in erased proofs. `OrderValid` fixes containment and the subject/embedding;
`transport_lt` and `sign_transport` require both providers for that same subject.
Predecessor order preservation additionally needs the explicit monotonicity
hypothesis in `C_lt`.

Infinitesimal interpretations compose the existing rational-function equivalence
with the Laurent/Hahn embedding. `embed_fraction` and `sign_fraction` keep the
original denominator's nonzero premise; normalization does not erase a caller's
source-expression divisor obligation. Lowest-coefficient, zero/top, valuation
and coefficient-embedding laws prove the native sign/order correspondence.
The Hahn model is not asserted real closed, and the two-level interpretation is
not an ordinary-real realization of a general tower.

These field-construction claims have Lean-checked homomorphism, injectivity and
native-dictionary evidence. No external arithmetic oracle, new axiom or chosen
semantic real is used as a runtime implementation.

## Phase criteria and validation

| Requirement | Evidence and disposition |
| --- | --- |
| Per-declaration API quality | All 147 handwritten declarations are matched to the existing individual assessment; the two fields, named instances and 33 public retention decisions are addressed above. |
| Characterizations and generality | Stored-fraction evaluation, arbitrary successful trials, separate progress assumptions, same-subject transport, arbitrary fraction presentations and ordered coefficient maps have public lemmas with explicit hypotheses. |
| Automation/imports/naming | The existing quality assessment applies. Local/scoped instances retain the intended dictionary; constructor/sign normalization uses simp, while unbounded progress and conditional semantic witnesses remain explicit. Generic sign laws import the generic sign layer. |
| Lint and documentation | The existing `HexOrderedFnTheory.LintTests` checks the public computational and companion roots with theorem documentation. Public declarations, the two fields and non-obvious private helpers meet the documentation rule. |
| Dead implementation helpers | Each of the six private helpers has the recorded proof consumers; the public zero-reference cases are intentional characterized API, not unused implementations. |
| Computational regression | The owning SPEC assigns runtime algorithms and benchmarks to `HexOrderedFn`; this semantic library has no compiled benchmark track under the Phase-4 policy. Existing theorem-application timings remain diagnostic. No computational performance pass is inferred. |
| Native execution and field evidence | The core dictionary identity, erased progress construction and existing 23-case compiled Liouville integration establish the actual execution route. Localization, Hahn and field/order transfer use Lean proofs as described above. |
| Ordinary-kernel trust | All 292 owned compiled constants have only `propext`, `Classical.choice`, `Quot.sound` as axioms. The existing kernel-built tests and source/admission audits reject proof holes, new axioms and `native_decide`. |
| User documentation | The partner chapter includes the correspondence section, source-derived signatures and compiled examples; current rendered desktop/mobile inspection includes finite signs, registration, successive infinitesimals and the genuine Liouville provider. |

The current build completes the public companion, complete `HexOrderedFnTests`
target, lint diagnostic, manual and `hexorderedfn_liouville_test`. The executable
reports all 23 integration cases passed, covering total sign, approximation,
formal zero, comparison, provider transport, native dictionary arithmetic and
successive approximation. These are correctness checks, not measurements.
The manual renderer succeeds, and its 1440px and 390px views retain readable
examples and no document overflow. The full monorepo build completes 14,629 jobs. The import/DAG checks,
phase/manual checks and admission audit pass; the latter scans 587
adapter/conformance cones and 1,487 local modules without admissions.
The unchanged compiler archive also passes its current-source verification.

The [companion SPEC](../../SPEC/Libraries/hex-ordered-fn-theory.md#conformance-and-phase-4-evidence)
and [Phase-4 policy](../../PLAN/Phase4.md#theory-libraries) assign this library
semantic proof tests, rather than a computational benchmark baseline.
[Local phase coupling](../../PLAN/Conventions.md) permits its Phases 6–7 without
promoting `HexOrderedFn` or any transitive input. The core's four retained
regression findings remain in the existing
[performance follow-up](../bench-results/ordered-fn-regression-followup/README.md).
General tower realization, BKR/tactic algorithms, candidate package preparation
and publication prerequisites retain their separate owners and requirements.
