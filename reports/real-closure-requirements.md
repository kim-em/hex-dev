# Real-closure integration requirements

This preparation audit accompanies [#10575](https://github.com/kim-em/hex-dev/issues/10575).
Its source base revision, input digest and recorded phases are in the
[package inventory](real-closure-package-inventory.json). It covers the family
requirements in [future-work](../SPEC/future-work.md#real-closures-of-ordered-fields),
the [execution contract](../SPEC/real-closure-execution.md), the eight owning
SPECs below and the [real-coefficient RCF contract](../HexRCF/SPEC/hex-rcf.md#planned-real-coefficient-extension).
It is an index of delivered contracts and remaining acceptance work, not
final acceptance or a substitute for owner attestation. Names below refer to
merged source unless a PR is explicitly identified as pending.

Successful example output establishes a fixture result. It does not establish
general producer success, arbitrary-certificate soundness, exact multiplicity,
all-live transport, or joint ordinary-real realization. Interpretation laws
and caller hypotheses remain explicit throughout this audit.

## Shared computation and Sturm pair

Owning SPECs: [Sturm](../HexSturm/SPEC/hex-sturm.md),
[SturmMathlib](../HexSturmMathlib/SPEC/hex-sturm-mathlib.md).

| Requirement | Actual operation and proof | Tests / independent evidence | Acceptance status |
| --- | --- | --- | --- |
| Shared operation-only polynomial kernels and semantic equality | `DensePoly` and `HexPolyMathlib.Interpret`; zero reflection and arithmetic preservation, without injectivity or a field instance on representatives | `HexPoly.InterpretTests`; noncanonical instantiations in sign conformance | Delivered interface; preserve the computation/companion boundary during migration |
| Valid open domains, finite/infinite endpoints, constant heads and refusal | `Sturm.prepare`, `query`, `rootCount`; `HexSturmMathlib.Domain`, `query_isSome`, `prepare_isSome` | `conformance/HexSturm`, including endpoint and replay tests | Domain correspondence delivered; [#10577](https://github.com/kim-em/hex-dev/issues/10577) owns readiness |
| Arbitrary certificate soundness and prepared query reuse | `Sturm.check`, `queryPrepared`, `countPrepared`; `Tarski.check_rootSum`, `HexSturmMathlib.check_sound`, `queryPrepared_sound`, `countPrepared_sound` | `conformance/HexSturmMathlib`; new `RealClosureConsumer.Query` checks domain plus value and prepared cardinality | Delivered in the ordinary companion target and public umbrella; caller interpretation/sign laws required |
| Producer acceptance and natural root counts | `certify_checks`, `certifyPrepared_checks`, `rootCount_isSome`, `rootCount_query`, `rootCount_map`, `query_nonneg` | `HexSturmMathlib` conformance and axiom inventories | Delivered, including combined `query_spec` and positive-clear `rootCount_sturm` from merged #10580; the exact `query_iff` headline from merged [#10660](https://github.com/kim-em/hex-dev/pull/10660) is exposed by the companion umbrella |
| Integer/dyadic agreement after positive denominator clearing | Existing integer `ZPoly.tarskiQuery` and shared Tarski kernel; frontend agreement and domain coverage | `HexRealRoots.TarskiTests`, `HexRealRootsMathlib.TarskiTests`; #10580 adds natural-count agreement and semantic guards | Merged #10580 supplies the finite-dyadic agreement; the generic rational frontend retains its infinite endpoints |
| Scaling, comparators, prepared-query memory and attribution | Compiled Sturm/query producers, distinct construction/replay tracks | [Sturm report](hex-sturm-performance.md); [#10577](https://github.com/kim-em/hex-dev/issues/10577) retains further unpublished audit/evidence | Owner attestation incomplete; historical samples and successful fixtures are not a Phase-4 pass |

The shared Tarski proof belongs to
[HexRealRootsMathlib.TarskiSoundness](../HexRealRootsMathlib/TarskiSoundness.lean).
The frontend domain/producer laws are in
[Domain](../HexSturmMathlib/Domain.lean), and root-sum/count semantics in
[Soundness](../HexSturmMathlib/Soundness.lean).

## Sign-determination pair

Owning SPECs: [SignDet](../HexSignDet/SPEC/hex-sign-det.md),
[SignDetMathlib](../HexSignDetMathlib/SPEC/hex-sign-det-mathlib.md).

| Requirement | Actual operation and proof | Tests / independent evidence | Acceptance status |
| --- | --- | --- | --- |
| Recursive BKR moments, support, retained rank and exact counts | `Reduction.build`, `QueryReduction.build`, tree/system builders; `Reduction.build_checks`, `QueryReduction.check_signs`, `System.retained_rank`, `solveScaled_eq`, `buildTree_complete` | `conformance/HexSignDetMathlib`, noncanonical reduction tests; `sign_det_flint.py`, `sign_det_z3.py` | Finite algebra and correspondence delivered; rank producer prerequisite attested by [#10352](https://github.com/kim-em/hex-dev/issues/10352) |
| Root/table producer success from a lawful domain | `Descriptor.build`, `validate`, `buildRoots`; `Descriptor.build_success_formal`, `validate_success_formal`, `buildRoots_success`, `buildRoots_isSome` | `RootSemantics`, `SelectedProducerConformance`, `TableConformance`, `ThomRootsConformance`; new `RealClosureConsumer.Sign` | Delivered development semantics, not only conditional checker soundness |
| Thom uniqueness, complete coverage and strict order without rational separators | Descriptor full derivative word, `fullOrder`, complete root list; `RawDescriptor.full_unique`, `full_lt`, `Descriptor.buildRoots_roots` | `ThomConformance`, `ThomRootsConformance` (0 and ε in one interval), Z3 infinitesimal oracle | Delivered under an explicit ordered real-closed model, including non-Archimedean fields |
| Selected sign, changed defining polynomial and comparison | `buildSigns`, `signAt`, reencoding and comparison producers; `buildSigns_success`, `signAt_correct`, checked conversion/root preservation | `ReencodingConformance`, `RefinementConformance`, `ComparisonConformance`, `ConvertConformance` | Delivered contracts retain embedding/input premises; do not infer joint real realization |
| Shared serialized coefficient evidence, exact contexts and checked cross-level conversion | Integer-only JSON codec, selected-sign records, context-bound proof facts and `HexRealClosure.SignFacts` finite proof assembly | `GraphSignsConformance`, `PackingConformance`, `NestedSignsConformance`, byte roundtrip/rejection fixtures; [JSON byte report](sign-det-json-bytes.md); `sign_det_json_bytes.py` | Merged [#10615](https://github.com/kim-em/hex-dev/pull/10615)/[#10617](https://github.com/kim-em/hex-dev/pull/10617)/[#10632](https://github.com/kim-em/hex-dev/pull/10632)/[#10656](https://github.com/kim-em/hex-dev/pull/10656)/[#10659](https://github.com/kim-em/hex-dev/pull/10659) supply strict finite readers, same-level sharing, child packets and byte bounds. [#10663](https://github.com/kim-em/hex-dev/pull/10663) adds stored-coefficient/context coverage; [#10664](https://github.com/kim-em/hex-dev/pull/10664) adds operation memo transport and cached replay equality. Automatic intermediate-key coverage, reconstructed cross-level contexts and compiled no-search replay remain with #10377 |
| BKR/Thom production and replay scaling, height, witness growth and allocation | Actual compiled builders/checkers and matrix operations | [joint](sign-det-joint-performance.md), [height](sign-det-height-model.md), [nested](sign-det-nested-fields.md), [matrix allocations](sign-det-matrix-allocations.md), [height allocations](sign-det-height-allocations.md) | Retained evidence exists; remaining performance requirements and Phase-4 attestation belong to [#10377](https://github.com/kim-em/hex-dev/issues/10377) |

Mathematical BKR algebra is already exposed by `HexSignDetMathlib`. Selected
semantics and producer laws remain in [its adapters](../adapters/HexSignDetMathlib).
Do not promote those additional imports merely because the ordinary umbrella
builds. Exact package ownership is in the publication proposal.

## Ordered-function pair

Owning SPECs: [OrderedFn](../HexOrderedFn/SPEC/hex-ordered-fn.md),
[OrderedFnMathlib](../HexOrderedFnMathlib/SPEC/hex-ordered-fn-mathlib.md).

| Requirement | Actual operation and proof | Tests / independent evidence | Acceptance status |
| --- | --- | --- | --- |
| Exact approximations and successful finite signs | `Real.enclose`, `finiteAttempt`, `sign?`, `approxAttempt`; `enclose_sound`, `finiteAttempt_sound`, `sign?_sound`, width/containment theorems | `HexOrderedFnMathlib.Tests`, `LiouvilleTests`, `conformance/HexOrderedFn`; `ordered_fn_real.py` | Delivered; finite success needs certified containment and denominator nonvanishing |
| Total signs and approximation search for caller-supplied constants | `Real.sign`, `approx`, registered `Extension`; `attempt_progress`, `sign_acc`, `approx_acc`, `Extension.sign_eq`, `compare_eq` | Compiled Liouville integration; original divisor and wrong-subject tests | Delivered conditional on relative transcendence over the entire predecessor field plus source containment/width laws; no bundled π/e provider |
| Infinitesimal positivity, comparisons, successive levels and ordered coefficient transport | `Infinitesimal.sign`, `compare`, `RationalFn.map`; Hahn `embed`, `X_pos`, `X_lt_C`, `X_lt_pow`, `mapHom_sign`, `mapHom_strictMono` | `InfinitesimalTests`, corrected Example-3 factor identity; `ordered_fn_z3.py`; new ordinary umbrella consumer | Delivered; the new consumer consumes order laws, not a nonstandard-analysis tactic |
| Computational Phase 4 and companion proof policy | Scan, arithmetic, Horner, real refinement, two-/three-level approximation families | [OrderedFn report](hex-ordered-fn-performance.md), retained raw data, Z3/FLINT ratios and representative profiles | [#10376](https://github.com/kim-em/hex-dev/issues/10376) complete; report has no concerns and both counters are 4. Tower clean/eager evidence is a distinct [#10378](https://github.com/kim-em/hex-dev/issues/10378) obligation |

The actual public umbrella is
[HexOrderedFnMathlib](../HexOrderedFnMathlib.lean). Caller approximation
laws justify interpreted computation; successful finite examples without
transcendence do not prove total sign search for arbitrary providers.

## Real-closure pair and integrated path

Owning SPECs: [RealClosure](../SPEC/Libraries/hex-real-closure.md),
[RealClosureMathlib](../SPEC/Libraries/hex-real-closure-mathlib.md).

| Requirement | Actual operation and proof | Tests / independent evidence | Acceptance status |
| --- | --- | --- | --- |
| Canonical zero with noncanonical nonzero storage, selected reducible roots | `Algebraic.Element.ofPoly`, zero/sign, local cofactor inversion; `denote_eq_zero`, `denote_ofPoly`, `cofactor_spec`, arithmetic/sign correspondence | `HexRealClosure.Tests`, `QAdjoinTests`, selected-root conformance | Delivered slice; no field instance on raw quotient representatives |
| Clean monic retention, non-monic/raw policy and value preservation | `Context.reduce`, `queryPoly`, element packing; `evalPoly_reduce`, clean companion laws, `reduce_nonmonic`, `reduce_unclean` | Algebraic tests and non-monic isolation fixtures | Delivered policies; do not treat scaled pseudo-remainders as value-preserving remainders |
| Yun decomposition, zero/all, constants, termination, multiplicities and order | `Roots.roots`, `Context.roots`, `roots?`; `Roots.roots_success`, `Context.roots_all`, `roots?_success`, `roots_spec`, `roots_sorted` | `RootFactorsTests`, `TowerRootsTests`; `real_closure_deflation.py`, `real_closure_isolation.py`; new `RealClosureConsumer.Tower` | Delivered under a common model; consumer composes success and exact multiplicities without assuming successful output |
| Root extensions, coefficient embeddings and stored native values | `Context.adjoin`, `Root.embed`, root materialization; `Model.adjoin_embed`, `Root.embed_value`, `convertedValue_value`, `signAt_value` | `TowerModelTests`, `TowerRootsTests`, isolation oracle | Delivered selected embeddings, separate from joint ordinary-real realization |
| Persistent refinement, all requested live dependency closure and general enlargement | Context/refinement/conversion APIs; `TowerTransport`, rebuilt suffix model and selected-root preservation | `TowerTransportTests`, `TowerRefinementTests`, changed-context rejection | Merged [#10651](https://github.com/kim-em/hex-dev/pull/10651)/[#10654](https://github.com/kim-em/hex-dev/pull/10654)/[#10655](https://github.com/kim-em/hex-dev/pull/10655) supply shared owner maps, real-prefix inclusions and ambient/base models. `Shared.enlarge?_models` preserves all original values assuming coherent `Inclusions.Models`; automatic coherent gathering/rebuilds in [#10662](https://github.com/kim-em/hex-dev/pull/10662)/[#10665](https://github.com/kim-em/hex-dev/pull/10665) remain pending |
| New infinitesimal below all transported positive old values | `Context.enlargeWithParameter?`; `enlargeWithParameter?_model`, `_ordered`, `_algebraic` | `TowerEnlargeOrderTests`: successive square roots, old inverse/gaps and preceding infinitesimal | Delivered for the actual returned conversion; not total all-live enlargement |
| Compatible algebraic union and real-closedness | `Union`, `TowerUnion`, relative ambient model; union real-closedness and common extension | `UnionTests`, `TowerModelTests` | Native finite `Presentation` quotient bijection, algebra equivalence and real-closedness merged in [#10616](https://github.com/kim-em/hex-dev/pull/10616); gathered-union identification in [#10667](https://github.com/kim-em/hex-dev/pull/10667) is pending |
| Sections/sectors, original-model signs and joint ordinary-real realization | Complete root families and sample/sector contracts | Native sample API and exact sample families from merged [#10607](https://github.com/kim-em/hex-dev/pull/10607); `SpecializeSample.realizeReplay` for one rational-function infinitesimal step | Local section/sector coverage, actual interpretation and sector sign constancy delivered. One-step realization assumes an ordered real embedding of the base; joint nested algebraic/infinitesimal realization remains with #10378 |
| Independent trivial-base fast path agreement | `Trivial.Rational.roots`; `Trivial.Rational.roots_eq`, `compare_eq` | `TrivialTests`, real-algebraic root/multiplicity/order conformance | Full native rational tower conversion, root/multiplicity/order, arithmetic and inverse agreement merged in [#10624](https://github.com/kim-em/hex-dev/pull/10624) with independent FLINT cases; broader registered/algebraic base coverage remains with #10378 |
| Reconstructible printing, registered constants and exploration/number-field integration | Base/context/element codecs, `FrameFormat`; `read_write`, `read_stale`, exact registry/signature bindings | `CodecTests`, `BaseCatalogTests`, `FrameFormatTests`; nested read/replay fixtures | Codec slices delivered; full exploration and number-field audit remains with [#10378](https://github.com/kim-em/hex-dev/issues/10378). Registry names must resolve to the same caller-supplied source |
| Nested evidence and adversarial cases | Actual α²=2+ε₁, β²=α+ε₂ selected-sign fixture; selected inversion, shared prepared domain and literal context checks | `conformance/HexRealClosure/NestedReplay.lean`; changed consumers, cycles, stale contexts and zero/wrong denominators; isolation oracle | Functional evidence merged in [#10610](https://github.com/kim-em/hex-dev/issues/10610); no joint-realization or computational scaling attestation |
| Corrected paper Example 3, tower8, MetiTarski, Rioboo/Strzeboński, clean/eager and representative attribution | Ordinary native tower/root algorithms | [arithmetic experiments](hex-real-closure/general-arithmetic.md), [isolation anchors](hex-real-closure/isolation-anchors.md), [storage experiment](real-closure-storage-experiments.md), owner conformance | Anchors/prototypes are retained, not complete required controlled evidence. [#10378](https://github.com/kim-em/hex-dev/issues/10378) must supply full source-matched schedules and attest Phase 4 |

The consumer supplies a `Tower.Model` explicitly. Model existence and transport
are separate theorems; a model over a non-Archimedean real closed field does
not itself produce ordinary-real values for nested infinitesimal samples.
The consumer contains no new algorithm or replacement for the owner's API
examples. Complete end-to-end constant → infinitesimal → algebraic extension
→ enlargement → reconstructible printing → ordinary-real tactic acceptance
remains open across these rows.

## Optional RCF and prerequisite evidence

| Requirement | Delivered operation/proof and reusable evidence | Remaining requirement |
| --- | --- | --- |
| Rational surface and original closed divisor guards | `import HexRCF`; `Certificate.check_sound`, decision/reification tests and [rational performance report](hex-rcf-performance.md) | Preserve ordinary rational import and fast-path agreement when optional packaging changes |
| Authenticated real coefficients, fixed selected fields and total library production | `HexRCF.RealCoefficients`; `LiteralSign.Table`, `FieldBuildProgress`, `FieldDecisionProgress.forall_decision`/`exists_decision`, `FieldBuildBudget` | Merged [#10618](https://github.com/kim-em/hex-dev/pull/10618)/[#10650](https://github.com/kim-em/hex-dev/pull/10650)/[#10658](https://github.com/kim-em/hex-dev/pull/10658) authenticate fixed-field conversion and interval signs. [#10661](https://github.com/kim-em/hex-dev/pull/10661) adds positional checked sign keys, `FieldLiteral.replay`, rollback and kernel tests. [#10668](https://github.com/kim-em/hex-dev/pull/10668)’s public `Coefficients.prepare`, `Specialize.prepare` and `Replay.Input` are pending; general source certification and the degree-8 common-field quotation gap remain with #10358 |
| Optional tactic proofs and refusal diagnostics | Reuse `conformance/HexRCF/TotalAlgebraicProofs.lean`, `ProductionProgress.lean` and manual examples; exact axiom guards and original zero-divisor rejection | No duplicate manual/example owner here. [#10358](https://github.com/kim-em/hex-dev/issues/10358) retains certification, joint-realization consumption and integrated scaling/sharing evidence |
| Rank correctness, performance and proof track | `rankCertWith_check`, `checkRank_sound`, `rankWith_eq`; [rank report](hex-rank-performance.md) and ten axiom-guarded CI probes | [#10352](https://github.com/kim-em/hex-dev/issues/10352) complete through [#10579](https://github.com/kim-em/hex-dev/issues/10579)/[#10584](https://github.com/kim-em/hex-dev/issues/10584); counters 4. Their own Phases 5–7 remain separate distribution work |
| Real-algebraic/Sturm prerequisites | Existing `compare_eq`, real root completeness/multiplicity/order, query/root-count semantics | #10580 merged with four Phase-3 counters and proved semantic contracts. [#10660](https://github.com/kim-em/hex-dev/pull/10660)’s stronger headlines and evidence are merged; Phase 4 remains incomplete. Public companion integration can proceed now and precedes Sturm’s API attestation |

Two-formula proof-cost observations in
[RCF production proofs](hexrcf-production-proofs.md) are retained diagnostics,
not computational scaling or full extension evidence. Companion theorem
applications follow current [Phase 4](../PLAN/Phase4.md) with representative
CI-built proofs and kernel axiom audits. New experiments need a concrete
unresolved decision; none is dispatched by this audit.

## Unresolved requirements and ownership

- **[#10577](https://github.com/kim-em/hex-dev/issues/10577):** Remaining Phase-4 input-axis/comparator/attribution requirements. #10580 and [#10660](https://github.com/kim-em/hex-dev/pull/10660) are merged; `query_iff` and `RealAlgebraicPoly.roots_spec` are proved headlines, and this migration makes the Sturm headline available through the actual companion. Parent closure is not a start gate. Operational CI cap failures are not performance passes.
- **[#10377](https://github.com/kim-em/hex-dev/issues/10377):** automatic intermediate arithmetic packing keys, complete cross-level sharing and validated context reconstruction, strict compiled missing-evidence rejection without producer calls, independent conformance and BKR/Thom Phase 4. `Codec.FiniteGraph` and `SignEvidence.codec_covered` cover stored coefficients and contexts, not every intermediate arithmetic result. `Dag.validateCached_eq` proves literal agreement, but the compiled fallback still performs native sign production at the opaque `Element.missing` boundary. Pending [#10671](https://github.com/kim-em/hex-dev/pull/10671) transports operation contexts; it does not itself complete that replay contract.
- **[#10378](https://github.com/kim-em/hex-dev/issues/10378):** automatic coherent live gathering/rebuilds and general refinement/dependency transport, joint ordinary-real realization of nested finite conjunctions, broader registered/algebraic-base agreement, exploration/number-field completion, required tower workloads/clean-eager evidence and Phase 4. [#10607](https://github.com/kim-em/hex-dev/pull/10607)/[#10616](https://github.com/kim-em/hex-dev/pull/10616)/[#10624](https://github.com/kim-em/hex-dev/pull/10624) are merged and reusable now. Pending [#10662](https://github.com/kim-em/hex-dev/pull/10662)/[#10665](https://github.com/kim-em/hex-dev/pull/10665)/[#10667](https://github.com/kim-em/hex-dev/pull/10667)/[#10669](https://github.com/kim-em/hex-dev/pull/10669) address model factories, cached gathering, union identification and existing-root reuse; none is treated as delivered here.
- **[#10358](https://github.com/kim-em/hex-dev/issues/10358):** complete coefficient/source certification and quotation (including the degree-8 common-field gap), consumption of actual nested joint-realization laws, and integrated tactic sharing/scaling evidence. Pending [#10668](https://github.com/kim-em/hex-dev/pull/10668) exposes authenticated preparation and finite replay; this audit does not copy its modules. The merged exact-field producer and quantified decision theorems are reusable now.
- **[#10575](https://github.com/kim-em/hex-dev/issues/10575):** final integrated acceptance tests, the eight libraries’ substantive Phases 5–7 proof/API/Verso work, remaining owner-safe adapter migration, an agreed optional package boundary, fresh candidate consumers and exact eligible publication changes. Shared Tarski/Sturm migration removes the specific public-import gap without attesting the other owners’ completion.

Distribution requirements are separately enumerated in the
[publication plan](real-closure-publication.md), including unreleased phase-1
inputs, rank/real-algebraic Phases 5–7, [#9809](https://github.com/kim-em/hex-dev/issues/9809), mirror bootstrap and full dry run.
