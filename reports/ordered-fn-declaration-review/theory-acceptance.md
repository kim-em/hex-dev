# OrderedFn Theory proof and manual acceptance

`HexOrderedFnTheory` satisfies Phases 6–7 independently of `HexOrderedFn`.
The computational library remains at Phase 5 with its retained regression
findings. The polishing adds public characterizations and simplification rules without
changing executable operations, existing theorem statements, package requirements
or publication eligibility.

## Scope and individual review

The [individual semantic assessment](companion.md), together with the four
additional characterizations reviewed below, covers every handwritten nontrivial
definition, theorem and named instance in the nine production modules. The [import and automation assessment](quality.md) records the shared
sign layer, scoped instances, characterizing lemmas and normalization choices.
Those assessments are reused here; a linter or reference count does not replace
them. The two sign lemmas moved to `Sign` without changing their public names or
proofs. The bare `mul_bounds` row in the Oracle assessment refers to
`Hex.OrderedFn.Oracle.Contains.mul_bounds`.

The inventory cross-check accounts for 151 handwritten declarations, including
four named field/order instances. The module totals below combine the older
individual assessment with the four additions reviewed in this report. The two projections of `ApproximationCorrect`
are assessed with that structure: coefficient and constant containment bind the
same provider, embedding, subject and positive request. The current CI-built
axiom audit checks every owned compiled constant, including generated declarations.
Counts describe the environment; they are not quality or performance gates.

| Module | Handwritten declarations | Individual assessment |
| --- | ---: | --- |
| `Convergence` | 11 | [Assessment](companion.md#convergence) |
| `Evaluation` | 10 | [Assessment](companion.md#evaluation) |
| `Extension` | 36 | [Assessment](companion.md#extension) |
| `Hahn` | 10 | [Assessment](companion.md#hahn) |
| `Infinitesimal` | 47 | [Assessment](companion.md#infinitesimal) |
| `Oracle` | 17 | [Assessment](companion.md#oracle) |
| `Progress` | 7 | [Assessment](companion.md#progress) |
| `Real` | 11 | [Assessment](companion.md#real) |
| `Sign` | 2 | [Assessment](companion.md#oracle) |

The [source and compiler archive](current/README.md) binds the pre-polishing
capture to `audit/issue-10575-orderedfn-current-input-v7` and
`audit/issue-10575-orderedfn-current-complete-v7`. Its tags and artifacts remain
unchanged. Reproduction uses an isolated complete-tag checkout; current-source
verification intentionally refuses the subsequent changes described here.
The existing individual assessments are supplemented by these API decisions:

| Declaration/change | Review and application |
| --- | --- |
| `Hahn.ofLex_mapHom` | Definitional bundled-map characterization; makes support, exponent and leading-coefficient simplification available on the public homomorphism. |
| `Hahn.map_coeff` | Definitional coefficient characterization of the actual homomorphism; used in `map_lt` instead of unfolding it. |
| `Hahn.map_single` | General monomial characterization from Mathlib’s map theorem; specializes to the existing `map_C`. It supplies the single simp rule for both. |
| `Infinitesimal.towerEmbed_X` | Composes the outer rational-function embedding with the coefficient embedding; `map_one` identifies its coefficient. |
| Simplification rules | Unconditional support/order/leading-coefficient, sign, constant-order and same-subject evaluation transport laws normalize their left sides. Environment lint checks simp normal forms. Conditional progress and semantic witness selection remain explicit. |
| Universes and formatting | Universe parameters are explicit; long production lines are wrapped. Existing public names and comparison-iff directions remain for downstream compatibility. |

The mixed two-level example interprets `C ε + δ` as the sum of an outer
constant with inner coefficient `embed ε` and the outer exponent-one monomial.
It combines addition and both generator characterizations. This checks composition of the
iterated Hahn generator characterizations, without claiming an independent order
proof. `X_lt_pow` proves the successive-level inequality by another route.
The current lint target rejects an owned axiom declaration or any dependency
outside `propext`, `Classical.choice`, `Quot.sound` for every constant attributed
to the production import closure, including the umbrella. It refuses missing or
unexpected modules and an empty constant selection.

## Public use and encapsulation

The ordinary `import HexOrderedFnTheory` exposes the real extension, generic sign
laws, convergence/evaluation/progress results and Hahn/infinitesimal model through
the existing umbrella. `RealClosureConsumer.successive_order` consumes
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

The 33 handwritten public declarations below had no retained named users in
the v7 captured environment, before the added simplification and model example. Their retention is an API-design judgment about the
individual contracts, not an assertion of production callers. Anonymous examples,
normalization and instance elaboration can leave no named edge; generated
aliases and tests can create edges. The four executable `main` modules omitted
from the single-environment capture and independent experimental Lake projects
remain outside its reference model.

The earlier 49-row table spans both libraries and a smaller import environment.
The v7 Theory subset has 33 rows; six Theory declarations gained downstream
users, including sign laws and `X_lt_pow`. This difference does not show that
every retained API gained a production caller.

These are promised characterizations of the public representations, embeddings,
orders and provider transport, rather than unused alternative algorithms. Keeping
them prevents consumers from unfolding implementation details. Existing anonymous
examples for registration, positivity and transport are reused. No tests are added
merely to manufacture named uses, and no useful interface is removed on a reference
count alone. This settles the companion's API-retention judgment separately from
the computational library's remaining acceptance.

| Public declaration | Retention judgment |
| --- | --- |
| `Real.RelativeTranscendence.ne_image` | Convenience elimination law: exclude any predecessor coefficient without constructing the polynomial witness. |
| `Real.evalHom_injective` | SPEC-required field-embedding API; avoids unfolding the localization construction. |
| `Real.evalHom_eq_ratFunc` | SPEC-required compatibility with Mathlib’s evaluator, with its documented same-universe restriction. |
| `Real.registration_source` | Convenience simp identity for extracting the registered source without unfolding registration. |
| `Real.Extension.coreField_eq` | SPEC-required identity of the native field dictionary; the definitional proof verifies implementation identity. |
| `Real.Extension.sign_neg` | Retain a direct public sign law for clients reasoning about negation, even though the order proof uses evaluation instead. |
| `Real.Extension.sign_mul` | Retain a direct public sign law, including zero, for clients composing multiplicative sign evidence. |
| `Real.Extension.sign_eq_zero_iff` | Public formal-zero characterization under the stated containment and relative-transcendence hypotheses. |
| `Real.Extension.compare_eq` | SPEC-required correspondence for all three executable comparison outcomes. |
| `Real.Extension.sign_pos_iff` | Convenience bridge between registered positivity and sign one. |
| `Real.Extension.sign_neg_iff` | Convenience bridge between registered negativity and sign minus one. |
| `Real.Extension.C_lt` | SPEC-required predecessor-order preservation with an explicit strict-monotonicity hypothesis. |
| `Real.Extension.eval_strictMono` | Convenience bundled monotonicity result for the proved native order. |
| `Real.Extension.OrderValid.strictOrderedRing` | Retain the standard Mathlib structure API without exposing an existential evaluation witness. |
| `Real.Extension.OrderValid.orderedRing` | Retain the corresponding core grind dictionary under the same order-validity evidence. |
| `Real.Extension.transport_lt` | SPEC-required order transport between two correct providers for the same subject and embedding. |
| `Real.Extension.sign_transport` | SPEC-required same-subject provider independence of total sign. |
| `Real.Valid.orderValid` | Convenience conversion from registration evidence to order validity without choosing witnesses again. |
| `Hahn.map_support` | SPEC-required coefficient-embedding characterization, including zero series. |
| `Hahn.map_leadingCoeff` | SPEC-required leading-coefficient transport at the preserved exponent. |
| `Hahn.map_le` | SPEC-required order transport including equality; keeps monotonicity explicit. |
| `Infinitesimal.embed_leadingCoeff` | SPEC-required valuation model characterization for nonzero stored fractions. |
| `Infinitesimal.embed_order` | SPEC-required exponent characterization with the essential nonzero-fraction hypothesis. |
| `Infinitesimal.sign_normalize` | SPEC-required normalization invariance, independent of representation details. |
| `Infinitesimal.sign_mul` | Public executable-sign multiplication law for arbitrary infinitesimal fractions. |
| `Infinitesimal.compare_eq` | SPEC-required correspondence for native three-way comparison. |
| `Infinitesimal.towerEmbed_lt` | SPEC-required iterated-Hahn order interpretation; separate from the successive-infinitesimal inequality proof. |
| `Infinitesimal.towerEmbed_C` | SPEC-required generator characterization; also used in the mixed two-level model example. |
| `Infinitesimal.orderedRing` | Retain the core grind dictionary alongside the standard Mathlib ordered-field interface. |
| `Oracle.Contains.ofDyadic` | SPEC-required dyadic-input containment API. |
| `Oracle.Contains.inter_isSome` | Convenience producer-success result from a common subject, without requiring the caller to guess intersection endpoints. |
| `Oracle.Contains.inter` | SPEC-required preservation of containment for any successful intersection. |
| `Real.sign?_sound` | SPEC-required arbitrary finite-output soundness, separate from search termination. |

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
| Per-declaration API quality | All 151 handwritten declarations are covered by the individual assessment and the four additions above; the two fields, named instances and 33 public retention decisions are addressed above. |
| Characterizations and generality | Stored-fraction evaluation, arbitrary successful trials, separate progress assumptions, same-subject transport, arbitrary fraction presentations and ordered coefficient maps have public lemmas with explicit hypotheses. |
| Automation/imports/naming | The existing quality assessment applies. Local/scoped instances retain the intended dictionary; constructor/sign normalization uses simp, while unbounded progress and conditional semantic witnesses remain explicit. Generic sign laws import the generic sign layer. |
| Lint and documentation | The existing `HexOrderedFnTheory.LintTests` checks the public computational and companion roots with theorem documentation. Public declarations, the two fields and non-obvious private helpers meet the documentation rule. |
| Dead implementation helpers | Each of the six private helpers has the recorded proof consumers; the public zero-reference cases are intentional characterized API, not unused implementations. |
| Computational regression | The owning SPEC assigns runtime algorithms and benchmarks to `HexOrderedFn`; this semantic library has no compiled benchmark track under the Phase-4 policy. Existing theorem-application timings remain diagnostic. No computational performance pass is inferred. |
| Native execution and field evidence | The core dictionary identity, erased progress construction and existing 23-case compiled Liouville integration establish the actual execution route. Localization, Hahn and field/order transfer use Lean proofs as described above. |
| Ordinary-kernel trust | All owned compiled constants have only `propext`, `Classical.choice`, `Quot.sound` as axioms. The existing kernel-built tests and source/admission audits reject proof holes, new axioms and `native_decide`. |
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
The earlier compiler archive remains reproducible at its immutable complete tag;
the new axiom check covers the current polished source. A local negative control
with a temporary proof hole in an owned Hahn theorem fails specifically on
`sorryAx`; restoring the byte-identical source restores a passing lint/axiom build.

The [companion SPEC](../../SPEC/Libraries/hex-ordered-fn-theory.md#conformance-and-phase-4-evidence)
and [Phase-4 policy](../../PLAN/Phase4.md#theory-libraries) assign this library
semantic proof tests, rather than a computational benchmark baseline.
[Local phase coupling](../../PLAN/Conventions.md) permits its Phases 6–7 without
promoting `HexOrderedFn` or any transitive input. The core's four retained
regression findings remain in the existing
[performance follow-up](../bench-results/ordered-fn-regression-followup/README.md).
General tower realization, BKR/tactic algorithms, candidate package preparation
and publication prerequisites retain their separate owners and requirements.
