# SignDet Theory proof and manual acceptance

`HexSignDetTheory` satisfies its independent Phases 6–7. `HexSignDet` remains
at Phase 5; its final computational acceptance is separate. This assessment
uses the completed owner contracts and the existing individual reviews. It
changes no algorithm, certificate contract, dependency or publication eligibility.

## Per-declaration review and source polishing

The [individual assessment](companion.md) treats all 228 handwritten declarations
in the 37 production modules, including the seventeen private helpers. The five
fields of `Node.Counted` have their [own dispositions](current/field-dispositions.md).
Generated equations, matchers, projections and proof helpers are accounted for
separately in the retained compiler evidence. A linter or reference count does
not replace these statement, proof and API-design judgments.

| Module | Handwritten declarations | Review |
| --- | ---: | --- |
| `Basis` | 8 | [Assessment](companion.md#basis) |
| `CommonProduct` | 4 | [Assessment](companion.md#commonproduct) |
| `ComparisonProducer` | 7 | [Assessment](companion.md#comparisonproducer) |
| `CompletionProducer` | 8 | [Assessment](companion.md#completionproducer) |
| `Convert` | 7 | [Assessment](companion.md#convert) |
| `DagSelectedSigns` | 3 | [Assessment](companion.md#dagselectedsigns) |
| `Derivatives` | 2 | [Assessment](companion.md#derivatives) |
| `Embedding` | 6 | [Assessment](companion.md#embedding) |
| `FiniteSolve` | 6 | [Assessment](companion.md#finitesolve) |
| `Foundation` | 5 | [Assessment](companion.md#foundation) |
| `Naturality` | 7 | [Assessment](companion.md#naturality) |
| `NodeBasis` | 8 | [Assessment](companion.md#nodebasis) |
| `NodeChecks` | 3 | [Assessment](companion.md#nodechecks) |
| `NodeProducer` | 6 | [Assessment](companion.md#nodeproducer) |
| `NodeSolve` | 2 | [Assessment](companion.md#nodesolve) |
| `ParentSystem` | 4 | [Assessment](companion.md#parentsystem) |
| `QueryHandle` | 5 | [Assessment](companion.md#queryhandle) |
| `QueryReduction` | 5 | [Assessment](companion.md#queryreduction) |
| `RationalSolve` | 6 | [Assessment](companion.md#rationalsolve) |
| `Reduction` | 9 | [Assessment](companion.md#reduction) |
| `ReductionProducer` | 3 | [Assessment](companion.md#reductionproducer) |
| `Reencode` | 3 | [Assessment](companion.md#reencode) |
| `ReencodingProducer` | 2 | [Assessment](companion.md#reencodingproducer) |
| `ReencodingRefinement` | 5 | [Assessment](companion.md#reencodingrefinement) |
| `RootList` | 8 | [Assessment](companion.md#rootlist) |
| `RootModel` | 11 | [Assessment](companion.md#rootmodel) |
| `RootProducer` | 10 | [Assessment](companion.md#rootproducer) |
| `SelectedProducer` | 5 | [Assessment](companion.md#selectedproducer) |
| `SelectedRoot` | 25 | [Assessment](companion.md#selectedroot) |
| `Solve` | 1 | [Assessment](companion.md#solve) |
| `TableProducer` | 5 | [Assessment](companion.md#tableproducer) |
| `Tensor` | 6 | [Assessment](companion.md#tensor) |
| `Thom` | 10 | [Assessment](companion.md#thom) |
| `ThomReencoding` | 2 | [Assessment](companion.md#thomreencoding) |
| `ThomRoots` | 7 | [Assessment](companion.md#thomroots) |
| `TreeChecks` | 3 | [Assessment](companion.md#treechecks) |
| `TreeSolve` | 11 | [Assessment](companion.md#treesolve) |

The [source manifest](manifest.json) binds the current reviewed modules while
preserving the original snapshot hashes. All production modules now disable
`autoImplicit`. Their universe parameters are explicit, and
`productVector_toList` explicitly binds its generic coefficient type. Long
production lines are wrapped within 100 columns. After removing these annotations
and the explicit binder, ignoring whitespace and the record field separator,
the statement and proof source agrees with the reviewed parent. The complete
companion builds under the stricter option; no implicit identifier has been
silently replaced by a different mathematical hypothesis.

Proof-client context hashes in the core assessments are refreshed only for the
audited Theory files. Core source and archived review hashes remain unchanged.
These are correspondence proofs for the existing executables, not new BKR,
Thom, tower or tactic implementations.

## Public contracts, automation and retained interfaces

The ordinary `import HexSignDetTheory` exports the root/table producers,
selected-root semantics, Thom ordering, checked conversion, prepared handles
and DAG selected-sign correspondence. The import closure has no tower input;
Tau Ceti remains confined to the Theory side of the dependency graph.

The interpretation is zero-reflecting and preserves the stated arithmetic and
sign operations. The stored carrier needs neither a field instance nor an
injective interpretation. Domain-only results omit real-closedness; root-count,
Thom and producer results state the real-closed target hypotheses they need.
Producer laws for inverse, negation and division remain explicit. No ordinary-real,
Archimedean or rational-separation premise is substituted for those contracts.

| Contract family | Public API and quality judgment |
| --- | --- |
| Complete tables | `determine_correct` covers every sign word, including omitted conditions. `determine_isSome`, `determinePrepared_success` and `buildTablePrepared_success` give producer/domain routes without assuming an output. These are distinct interfaces for callers with native production or accepted evidence. |
| Arbitrary replay | `Replay.check_domain`, `check_support`, `check_counts` and `count_roots` expose acceptance consequences without unfolding the recursive checker. Complete support precedes inverse-based count recovery; a matching total or a zero-dimensional system cannot replace it. |
| Checked descriptors | `validate_success_iff`, `build_success_iff`, `root_spec` and `root_unique` characterize literal context, well-formedness, full domain and the unique selected point. Empty constraints and partial derivative words retain their exact meaning. |
| Completion and signs | `complete_correct`, `buildCompletion_success`, `signAt_correct` and prepared-handle laws retain the original selected root and query order. Public success statements rule out diagnostic fallbacks under lawful coefficients. |
| Comparison | `compare_correct` and its three relation characterizations expose all outcomes, including different heads. Full derivative words and the checked squarefree common head supply the hypotheses; lexicographic word order is not root order. |
| Re-encoding | `buildReencoding_isSome`, invalid/absent cases, refinement and `Reencoding.root_eq_source` give callers precise success and transport laws. Retaining target validity, root membership and newly checked context prevents reuse of stale evidence. |
| Root lists | Actual `buildRoots_roots`, coverage and order are separate from `rootsFrom_coverage` and `rootsFrom_ordered` for supplied accepted replay. Linear/subsingleton specializations are convenient public APIs, not alternative algorithms. |
| Conversion and embeddings | Count, selected-sign, comparison and ordered-root congruence laws characterize the actual converted operations. `root_map` and `root_comp` preserve the selected point under ordered ambient embeddings; they construct no ordinary-real tower realization. |
| Local normalization | `rootObservations_take` and `rootObservations_drop` are simp rules preserving the shared root list. Matrix representation, finite count and endpoint laws have named interfaces. Conditional coefficient interpretations and recursive producer correctness stay explicit instead of becoming global rewrites that would invent semantic witnesses. |

The [64 public dispositions](current/public-dispositions.md) are adopted as
individual retention decisions under [the public-API rule](../../PLAN/Conventions.md).
They distinguish production callers, companion/evidence clients and no direct
references. The operation families above explain why these characterizations
remain supported. Convenience results such as endpoint conversion, root-list
linear/subsingleton cases, direct count projections and relation iff lemmas
save consumers from opening representations or reconstructing semantic witnesses.
They are intentionally retained interfaces even without a named production
consumer. This is an API decision, not evidence that every declaration has
acquired a caller.

All [seventeen private paths](current/helper-paths.json) lead to handwritten
public results. Their proof bodies and consumers are preserved by the source
comparison. No unused alternate handwritten implementation was identified.
The namespace and import review retains the existing short public names;
interpretation parameters and local `open` directives do not install field or
order instances on stored coefficients.

## Kernel trust and reference evidence

The [v10 compiler archive](current/README.md) remains byte-for-byte intact at
its source/complete tags. Its 453 attributed constants, reference graph and
source citations describe that larger imported environment. Default archive
verification remains valid. Current-source mode correctly refuses the later
source polishing; the archive is not presented as a new current-source capture.

The CI-built `Diagnostics.Lint` additionally checks every constant attributed
to the current production import closure, including the umbrella. It derives
that closure by module prefix and compares it in both directions with the
reviewed module list. It refuses missing/unreviewed modules, an empty selection,
owned axiom declarations and any axiom outside `propext`, `Classical.choice`,
`Quot.sound`.

The current root-only environment contains all 228 handwritten declarations,
all five fields and all seventeen private helpers. Its attributed generated
constants differ from the older, larger capture: eight lazily generated core
equations from the old environment are absent and an imported-domain equation
is present. Numerical constant counts are observations of an environment, not
coverage or quality gates. The current owned-constant check and the preserved
archive give their exact, distinct scopes.

A local negative control replaces the proof of `convert_endpoint` by a temporary
proof hole and is rejected specifically on `sorryAx`. Restoring byte-identical
source restores a passing lint/axiom build. Ordinary-kernel proof examples cover
producer success, arbitrary replay, noncanonical carriers and selected roots.
The existing source/admission audit additionally checks the integrated cones.

The environment lints include slow checks and theorem documentation. The
companion root is clean. The core root has an exact guard for five declarations
generated by the pinned deriving handler; it permits no handwritten exception
or additional diagnostic. This records the scope of the environment lint rather
than claiming every Mathlib syntax-style option is enabled.

## Phase criteria and documentation

| Requirement | Evidence and disposition |
| --- | --- |
| Individual API/proof quality | The 228 declaration assessments, five field judgments, seventeen private paths, source comparison and 64 explicit public retention decisions apply to the polished source. |
| Generality and encapsulation | The contract table above maps headline correctness, producer totality, arbitrary replay and selected-root transport to public characterizations with their semantic hypotheses. |
| Native computation | Production/checking and their algorithms remain in the computational library. The Theory supplies proofs; external CAS results and chosen mathematical roots are not runtime implementations. Existing compiled field checks and shared conformance fixtures remain the owner's evidence. |
| Field/irreducibility evidence | This library assumes its interpreted real-closed field and proves descriptor identity/order. It makes no field instance on a reducible quotient or a stored coefficient carrier, and introduces no new field-construction or irreducibility claim. |
| Applicable regression check | The owning SPEC assigns runtime comparisons to the Mathlib-free libraries and this companion to representative CI-built proof examples and axiom audits. It has no computational benchmark baseline. The retained BKR evidence remains required for the core; theorem timings supply no computational pass. |
| Manual | The partner chapter explains tables, descriptors, completion, signs, comparison, conversion and replay. Its correspondence section pulls `determine_correct` and `buildRoots_roots` from source, and the existing checked example obtains actual producer coverage without assuming success. |
| Imports and trust | The companion, declared proof roots, diagnostics and field proofs build through ordinary public imports. The DAG, Mathlib-free boundaries and source/admission checks remain part of integrated validation. |

The existing direct API and manual examples are reused. Tower realization and
tactic/manual deliverables retain their owners. The companion is unreleased;
its development README accurately describes ordinary development imports and
links the partner chapter. There is no anchored tutorial for this library.
The public companion, declared proof examples, diagnostics, field-proof consumers
and manual build complete 14,258 jobs. The full monorepo build completes 14,629
jobs. The source/assessment checks, preserved archive checker, DAG, phase/manual
checks and admission audit pass; the latter scans 587 cones and 1,487 local
modules without admissions. Rendered desktop and 390px inspection covers tables,
selected roots, shared evidence, conversions and the correspondence; document
width equals viewport width.

[Local phase coupling](../../PLAN/Conventions.md) permits the companion's
Phases 6–7 without advancing its computational partner or transitive inputs.
The [owning SPEC](../../HexSignDetTheory/SPEC/hex-sign-det-theory.md#conformance-and-phase-4-evidence)
and [proof-track policy](../../PLAN/Phase4.md#evidence-tracks) determine the applicable
validation. The family publication plan, transitive phase eligibility, mirror
creation and candidate-package checks remain separate requirements.
