# Real-closure integration requirements

This preparation audit accompanies [#10575](https://github.com/kim-em/hex-dev/issues/10575).
The [package inventory](real-closure-package-inventory.json) retains the separate
package-preparation source snapshot, input digest and phases. This requirements
index follows the merged APIs described below. It covers the family
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
| Valid open domains, finite/infinite endpoints, constant heads and refusal | `Sturm.prepare`, `query`, `rootCount`; `HexSturmMathlib.Domain`, `query_isSome`, `prepare_isSome` | `conformance/HexSturm`, including endpoint and replay tests | Domain correspondence delivered; [individual declaration review](sturm-declaration-review/README.md) covers the owned production modules. [#10860](https://github.com/kim-em/hex-dev/pull/10860) supplies owner Phase-4 readiness; [proof acceptance](sturm-proof-acceptance.md) records Phase 5 |
| Arbitrary certificate soundness and prepared query reuse | `Sturm.check`, `queryPrepared`, `countPrepared`; `Tarski.check_rootSum`, `HexSturmMathlib.check_sound`, `queryPrepared_sound`, `countPrepared_sound` | `HexSturmMathlibTests` and `HexQuerySemantics` semantic replay tests; `RealClosureConsumer.Query` checks domain plus value and prepared cardinality | Delivered in the ordinary companion target and public umbrella; caller interpretation/sign laws required |
| Producer acceptance and natural root counts | `certify_checks`, `certifyPrepared_checks`, `rootCount_isSome`, `rootCount_query`, `rootCount_map`, `query_nonneg` | `HexSturmMathlib/Tests*`, `adapters/HexSturmMathlib/Tests/Replay/Semantics*` and their axiom inventories | Delivered, including combined `query_spec` and positive-clear `rootCount_sturm` from merged #10580; the exact `query_iff` headline from merged [#10660](https://github.com/kim-em/hex-dev/pull/10660) is exposed by the companion umbrella |
| Integer/dyadic agreement after positive denominator clearing | Existing integer `ZPoly.tarskiQuery` and shared Tarski kernel; frontend agreement and domain coverage | `HexRealRoots.TarskiTests`, `HexRealRootsMathlib.TarskiTests`; #10580 adds natural-count agreement and semantic guards | Merged #10580 supplies the finite-dyadic agreement; the generic rational frontend retains its infinite endpoints |
| Scaling, comparators, prepared-query memory and attribution | Compiled Sturm/query producers, distinct construction/replay tracks | [Sturm report](hex-sturm-performance.md); [readiness matrix](real-closure-prerequisites.md) and retained source-scoped evidence | Owner Phase-4 attestation merged in [#10860](https://github.com/kim-em/hex-dev/pull/10860); performance limits and historical/inconclusive observations remain explicit |

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
| Recursive BKR moments, support, retained rank and exact counts | `Reduction.build`, `QueryReduction.build`, tree/system builders; `Reduction.build_checks`, `QueryReduction.check_signs`, `System.retained_rank`, `solveScaled_eq`, `buildTree_complete` | `conformance/HexSignDetMathlib`, noncanonical reduction tests; `sign_det_flint.py`, `sign_det_z3.py` | Finite algebra and correspondence delivered; [companion declaration review](sign-det-declaration-review/README.md) covers its 37 production modules without phase promotion; rank producer prerequisite attested by [#10352](https://github.com/kim-em/hex-dev/issues/10352) |
| Root/table producer success from a lawful domain | `Descriptor.build`, `validate`, `buildRoots`; `Descriptor.build_success_formal`, `validate_success_formal`, `buildRoots_success`, `buildRoots_isSome` | `RootSemantics`, `SelectedProducerConformance`, `TableConformance`, `ThomRootsConformance`; new `RealClosureConsumer.Sign` | Delivered development semantics, not only conditional checker soundness |
| Thom uniqueness, complete coverage and strict order without rational separators | Descriptor full derivative word, `fullOrder`, complete root list; `RawDescriptor.full_unique`, `full_lt`, `Descriptor.buildRoots_roots` | `ThomConformance`, `ThomRootsConformance` (0 and ε in one interval), Z3 infinitesimal oracle | Delivered under an explicit ordered real-closed model, including non-Archimedean fields |
| Selected sign, changed defining polynomial and comparison | `buildSigns`, `signAt`, reencoding and comparison producers; `buildSigns_success`, `signAt_correct`, checked conversion/root preservation | `ReencodingConformance`, `RefinementConformance`, `ComparisonConformance`, `ConvertConformance` | Delivered contracts retain embedding/input premises; do not infer joint real realization |
| Shared serialized coefficient evidence, exact contexts and checked cross-level conversion | Integer-only JSON codec, selected-sign records, context-bound proof facts, `HexRealClosure.SignFacts` finite proof assembly and `Dependencies.Graph.decode`/`codec_bytes`/`Decoded.results_bound` | `DependenciesConformance`, `GraphSignsConformance`, `PackingConformance`, `NestedSignsConformance`, byte roundtrip/rejection fixtures; [JSON byte report](sign-det-json-bytes.md); `sign_det_json_bytes.py` | [#10612](https://github.com/kim-em/hex-dev/issues/10612) is merged with its explicit opaque missing-fact boundary. The cross-level envelope supplies typed routing, literal bindings and byte roundtrip laws. Merged [#10758](https://github.com/kim-em/hex-dev/pull/10758) supplies generic coefficient/context reconstruction and paired byte readers with preserved acceptance/refusal. [#10861](https://github.com/kim-em/hex-dev/pull/10861) completes owner implementation, independent conformance and Phase-4 attestation for sign determination. Automatic reached-data assembly for the tower/tactic pipeline remains with their owners |
| BKR/Thom production and replay scaling, height, witness growth and allocation | Actual compiled builders/checkers and matrix operations | [joint](sign-det-joint-performance.md), [height](sign-det-height-model.md), [nested](sign-det-nested-fields.md), [matrix allocations](sign-det-matrix-allocations.md), [height allocations](sign-det-height-allocations.md) | Owner Phase-4 attestation is merged in [#10861](https://github.com/kim-em/hex-dev/pull/10861); retained findings, rejected/inconclusive observations and upstream numeral-construction limits remain explicit |

Mathematical BKR algebra, selected-root semantics and producer laws are
exposed by the normal [companion](../HexSignDetMathlib) and its
`HexSignDetMathlib` umbrella. Development availability does not attest owner
performance or publication eligibility. Exact package ownership and remaining
requirements are in the publication proposal.

## Ordered-function pair

Owning SPECs: [OrderedFn](../HexOrderedFn/SPEC/hex-ordered-fn.md),
[OrderedFnMathlib](../HexOrderedFnMathlib/SPEC/hex-ordered-fn-mathlib.md).

| Requirement | Actual operation and proof | Tests / independent evidence | Acceptance status |
| --- | --- | --- | --- |
| Exact approximations and successful finite signs | `Real.enclose`, `finiteAttempt`, `sign?`, `approxAttempt`; `enclose_sound`, `finiteAttempt_sound`, `sign?_sound`, width/containment theorems | `HexOrderedFnMathlib.Tests`, `LiouvilleTests`, `conformance/HexOrderedFn`; `ordered_fn_real.py` | Delivered; finite success needs certified containment and denominator nonvanishing |
| Total signs and approximation search for caller-supplied constants | `Real.sign`, `approx`, registered `Extension`; `attempt_progress`, `sign_acc`, `approx_acc`, `Extension.sign_eq`, `compare_eq` | Compiled Liouville integration; original divisor and wrong-subject tests | Delivered conditional on relative transcendence over the entire predecessor field plus source containment/width laws; no bundled π/e provider |
| Infinitesimal positivity, comparisons, successive levels and ordered coefficient transport | `Infinitesimal.sign`, `compare`, `RationalFn.map`; Hahn `embed`, `X_pos`, `X_lt_C`, `X_lt_pow`, `mapHom_sign`, `mapHom_strictMono` | `InfinitesimalTests`, corrected Example-3 factor identity; `ordered_fn_z3.py`; new ordinary umbrella consumer | Delivered; the new consumer consumes order laws, not a nonstandard-analysis tactic |
| Computational Phase 4 and companion proof policy | Scan, arithmetic, Horner, real refinement, two-/three-level approximation families | [OrderedFn report](hex-ordered-fn-performance.md), retained raw data, Z3/FLINT ratios and representative profiles | [#10376](https://github.com/kim-em/hex-dev/issues/10376) complete; the original Phase-4 report has no concerns; both counters are now 5 after the public API tranche [#10750](https://github.com/kim-em/hex-dev/pull/10750). The subsequent [API review](hex-ordered-fn-api.md) retains unresolved Phase-6 comparisons. Tower clean/eager evidence is a distinct [#10378](https://github.com/kim-em/hex-dev/issues/10378) obligation |

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
| Persistent refinement, all requested live dependency closure and general enlargement | Context/refinement/conversion APIs; `TowerTransport`, rebuilt suffix model and selected-root preservation | `TowerTransportTests`, `TowerRefinementTests`, changed-context rejection | Merged [#10651](https://github.com/kim-em/hex-dev/pull/10651)/[#10654](https://github.com/kim-em/hex-dev/pull/10654)/[#10655](https://github.com/kim-em/hex-dev/pull/10655) supply shared owner maps, real-prefix inclusions and ambient/base models. `Shared.enlarge?_models` preserves all original values assuming coherent `Inclusions.Models`; merged [#10662](https://github.com/kim-em/hex-dev/pull/10662) derives source/base owner models from a compatible target provider history through `BaseInclusion.Model.derive`, preserving the supplied target model. Merged [#10665](https://github.com/kim-em/hex-dev/pull/10665) supplies coherent gathering/cached rebuilds. Merged [#10762](https://github.com/kim-em/hex-dev/pull/10762) supplies `Tower.Shared.realize_values` through retained checked inclusions, actual gather success and a supplied base realization, constructing its symbolic reference internally; native provider reordering and `BaseReconciliation.Model.deriveCanonical` derive source realizations/models from the target alone; canonical owner lookup, cache consumers and joint target selection are integrated through the reconciled factories and validated-prefix catalog; canonical shared/live enlargement preserves these owners and caches through successive predecessor maps, with ordinary finite-inventory realization; assembly of a missing joint provider history remains open |
| New infinitesimal below all transported positive old values | `Context.enlargeWithParameter?`; `enlargeWithParameter?_model`, `_ordered`, `_algebraic` | `TowerEnlargeOrderTests`: successive square roots, old inverse/gaps and preceding infinitesimal | Delivered for the actual returned conversion; not total all-live enlargement |
| Compatible algebraic union and real-closedness | `Union`, `TowerUnion`, relative ambient model; union real-closedness and common extension | `UnionTests`, `TowerModelTests` | Native finite `Presentation` quotient bijection, algebra equivalence and real-closedness merged in [#10616](https://github.com/kim-em/hex-dev/pull/10616); gathered-union identification in [#10667](https://github.com/kim-em/hex-dev/pull/10667) is merged |
| Sections/sectors, original-model signs and joint ordinary-real realization | Complete root families and sample/sector contracts | Native sample API and exact sample families from merged [#10607](https://github.com/kim-em/hex-dev/pull/10607); `Specialize.realizeReplay` for one rational-function infinitesimal step | Local section/sector coverage, actual interpretation and sector sign constancy delivered. One-step realization assumes an ordered real embedding of the base; joint nested algebraic/infinitesimal realization remains with #10378 |
| Independent trivial-base fast path agreement | `Trivial.Rational.roots`; `Trivial.Rational.roots_eq`, `compare_eq` | `TrivialTests`, real-algebraic root/multiplicity/order conformance | Full native rational tower conversion, root/multiplicity/order, arithmetic and inverse agreement merged in [#10624](https://github.com/kim-em/hex-dev/pull/10624) with independent FLINT cases; merged [#10755](https://github.com/kim-em/hex-dev/pull/10755) retains original selected number-field coordinates through roots and samples. Broader registered-base coverage and the final evidence audit remain with #10378 |
| Reconstructible printing, registered constants and exploration/number-field integration | Base/context/element codecs, `FrameFormat`; `read_write`, `read_stale`, exact registry/signature bindings | `CodecTests`, `BaseCatalogTests`, `FrameFormatTests`; nested read/replay fixtures | Codec slices and original number-field integration (#10755) are delivered; complete serialization/exploration acceptance and the final evidence audit remain with [#10378](https://github.com/kim-em/hex-dev/issues/10378). Registry names must resolve to the same caller-supplied source |
| Nested evidence and adversarial cases | Actual α²=2+ε₁, β²=α+ε₂ selected-sign fixture; selected inversion, shared prepared domain and literal context checks | `conformance/HexRealClosure/NestedReplay.lean`; changed consumers, cycles, stale contexts and zero/wrong denominators; isolation oracle | Functional evidence merged in [#10610](https://github.com/kim-em/hex-dev/issues/10610); no joint-realization or computational scaling attestation |
| Corrected paper Example 3, tower8, MetiTarski, Rioboo/Strzeboński, clean/eager and representative attribution | Ordinary native tower/root algorithms | [arithmetic experiments](hex-real-closure/general-arithmetic.md), [isolation anchors](hex-real-closure/isolation-anchors.md), [storage experiment](real-closure-storage-experiments.md), owner conformance | [Reconciled Phase-4 report](real-closure-phase4.md) from merged [#10780](https://github.com/kim-em/hex-dev/pull/10780) indexes retained clean/eager and MetiTarski evidence, including inconclusive results and remaining obligations. The remaining-scope table there includes original Rioboo/Strzeboński inputs, `nlsat.py`/`basic.py` provenance, counters, certificate-sharing and trivial-path matched comparisons. Tower8 also needs an authoritative input/premise correction. Owner Phase-4 attestation remains open; no prototype or hash-verification run replaces it |

The consumer supplies a `Tower.Model` explicitly. Model existence and transport
are separate theorems; a model over a non-Archimedean real closed field does
not itself produce ordinary-real values for nested infinitesimal samples.
The consumer contains no new algorithm or replacement for the owner's API
examples. Complete end-to-end constant → infinitesimal → algebraic extension
→ enlargement → reconstructible printing → ordinary-real tactic acceptance
remains open across these rows.

The finite ordinary-real consumer boundary is concrete:
[`Transport.Finite.DescriptorData`](../adapters/HexRealClosureMathlib/TransportDescriptor.lean)
and [`Transport.Finite.ReplayData`](../adapters/HexRealClosureMathlib/TransportReplay.lean)
carry reached derivative, arithmetic, moment and reduction relations.
`Transport.Finite.selected` needs both descriptor data and the selected-sign
replay data for the descriptor queries extended by the new queries.

The supplied inverse interface has its own
[declaration review](real-closure-inverse-api.md).
`Packing.Inverse.Equation.readMemo?` checks the retained operand/output equation
without computing the native candidate. Its `eval_inv` law consumes reached
product/subtraction data; `atPoint` also consumes original packing replay and
descriptor data to retain the original equation, inverse law and both signs at
the shared finite point. Native inverse records and their finite data convert
to this interface without changing their literal replay. Existing
`InversePackingTests` covers supplied-reader acceptance and refusal separately
from the stronger native record. Automatic recursive premise assembly remains
distinct from these proved conditional laws and finite executable controls.

The relative route automatically covers original-owner descriptor inventories.
`Live.Collection.realize` and `Enlargement.realize`/`realize_model` provide their
agreement, and
[`Transport.Inventory.descriptor_data`](../adapters/HexRealClosureMathlib/TransportInventory.lean)
produces closed `Transport.DescriptorData`. Refreshed target-side descriptors
additionally require `Collection.inventory` as `extra`, or as `fresh` after an
enlargement. The owner's
[`collection_replay`, `enlargement_replay` and `target_replay`](../adapters/HexRealClosureMathlib/SharedRealizationTests.lean)
exercise these closed-data cases; `target_replay` explicitly passes that extra
inventory, and `enlargement_replay` covers original-owner descriptors.

Selected-sign replay machinery is also delivered: `Inventory.replay_data` and
`Finite.ReplayData.of_closed` supply the corresponding data when given agreement
for `Inventory.replay raw.head raw.lower raw.upper (raw.queries ++ qs) signs.evidence`.
That inventory must be requested through `extra`/`fresh`, or assembled by the
exporter; a frame does not store selected-sign records.
[`TransportFiniteTests.identity_point`](../adapters/HexRealClosureMathlib/TransportFiniteTests.lean)
uses the identity reader on ℝ, derives both closed-data forms, and applies the
finite conversions. Do not duplicate these delivered transport constructions.

The required direct `Sample.realizeReplay` theorem remains missing. Its inputs
are accepted finite replay evidence through interleaved algebraic/infinitesimal
stages and authenticated real base-coefficient evidence, without `Realizes model Γ`
or a relative ambient model. Reached finite arithmetic data and reached zero
packings must be built from that evidence, including selected-sign replay
inventories. General interleaved export assembly must then compose the returned
factory models and retained inclusions with this independent direct theorem.
Delivered `Specialize.realizeReplay` and `Specialize.selected_near` are one-step
ingredients with a supplied ordered real embedding of the predecessor; they are
not the recursive theorem. Relative realization chooses a new ordinary reader
rather than extending an earlier one.

The existing `separate_providers` example gathers an owner into a supplied,
already validated joint parent. Constructing arbitrary jointly compatible real
bases from incomparable key sets, and transporting permutations, remain open.
`KernelReplay.collectMany` authenticates supplied facts without filling these
assembly/realization obligations. `Tower.Shared.realize_values` supplies coherent
relative readers without discharging the complete exporter contract.

## Optional RCF and prerequisite evidence

| Requirement | Delivered operation/proof and reusable evidence | Remaining requirement |
| --- | --- | --- |
| Rational surface and original closed divisor guards | `import HexRCF`; `Certificate.check_sound`, decision/reification tests and [rational performance report](hex-rcf-performance.md) | Preserve ordinary rational import and fast-path agreement when optional packaging changes |
| Authenticated real coefficients, fixed selected fields and total library production | `HexRCF.RealCoefficients`; `LiteralSign.Table`, `FieldBuildProgress`, `FieldDecisionProgress.forall_decision`/`exists_decision`, `FieldBuildBudget` | Merged [#10618](https://github.com/kim-em/hex-dev/pull/10618)/[#10650](https://github.com/kim-em/hex-dev/pull/10650)/[#10658](https://github.com/kim-em/hex-dev/pull/10658) authenticate fixed-field conversion and interval signs. [#10661](https://github.com/kim-em/hex-dev/pull/10661) adds positional checked sign keys, `FieldLiteral.replay`, rollback and kernel tests. Merged [#10668](https://github.com/kim-em/hex-dev/pull/10668) supplies public `Coefficients.prepare`, `Specialize.prepare` and input-bound finite `Replay.check`, with `check_domains`, `check_spec`, `check_sound`, `check_original` and bounded/total producer acceptance. Reuse `PreparedCoefficients`, `FiniteReplay` and the fresh `ProofProbe.Prepared` kernel guards. Merged [#10866](https://github.com/kim-em/hex-dev/pull/10866) uses a supplied ordinary-kernel irreducibility proof for one degree-eight common field through the ordinary-import frontend. General automatic certification and frozen source assembly remain with #10358 |
| Optional tactic proofs and refusal diagnostics | Reuse `conformance/HexRCF/TotalAlgebraicProofs.lean`, `ProductionProgress.lean` and manual examples; exact axiom guards and original zero-divisor rejection | No duplicate manual/example owner here. [#10358](https://github.com/kim-em/hex-dev/issues/10358) retains certification, joint-realization consumption and integrated scaling/sharing evidence |
| Rank correctness, performance and proof track | `rankCertWith_check`, `checkRank_sound`, `rankWith_eq`; [rank report](hex-rank-performance.md) and ten axiom-guarded CI probes | [#10352](https://github.com/kim-em/hex-dev/issues/10352) complete through [#10579](https://github.com/kim-em/hex-dev/issues/10579)/[#10584](https://github.com/kim-em/hex-dev/issues/10584); counters 4. Their own Phases 5–7 remain separate distribution work |
| Real-algebraic/Sturm prerequisites | Existing `compare_eq`, real root completeness/multiplicity/order, query/root-count semantics | [#10860](https://github.com/kim-em/hex-dev/pull/10860) completes owner Phase-4 readiness for all four inputs. The query/root-count and real-algebraic root completeness/multiplicity/order APIs are proved. [Sturm proof acceptance](sturm-proof-acceptance.md) records Phase 5 for that pair; real-algebraic Phases 5–7 remain separate distribution work |

Merged [#10777](https://github.com/kim-em/hex-dev/pull/10777) adds
[`NumberField.runWith`, `runWith_spec`, `run`, `run_spec`, `run_total` and `run_true`](../adapters/HexRCF/RealCoefficients/NumberField.lean).
Native diagnostic production retains the original selected real embedding and
`QAdjoin` coordinates, with frontend coefficient agreement from
`value_eq_ofField` and `run_coefficients`. The owner's
[NumberField conformance](../conformance/HexRCF/NumberField.lean) and tactic/manual
examples supply the corresponding evidence. These total diagnostic APIs do not
establish frozen frontend certificate quotation or general nested realization.

Merged [#10698](https://github.com/kim-em/hex-dev/pull/10698) adds
`RepresentationSpecialize.prepare`, all-valuation `prepare_eval` and semantic
`prepare_degrees` for an authenticated native coefficient interpretation.
The owner's `TowerSamples` consumes actual selected-field `Sample.Family`
coverage and sign-vector laws, preserving original strict/non-strict guards,
zero atoms, repeated atoms and leading cancellation. This covers ordinary
samples over those selected coefficients; general joint nested realization
and a frozen tower tactic backend remain separate requirements. Merged
[#10692](https://github.com/kim-em/hex-dev/pull/10692) supplies checked
generator-window replay with fresh axiom-guarded owner probes. These are reused
owner APIs and examples, not duplicated here.

Merged [#10677](https://github.com/kim-em/hex-dev/pull/10677) supplies typed
cross-field dependency routing and byte roundtrip laws. The ordinary-kernel
serialized-graph prototype in [#10693](https://github.com/kim-em/hex-dev/pull/10693)
is retained experimental evidence; it does not discharge the missing compiled
strict replay/automatic arithmetic evidence contract.

Two-formula proof-cost observations in
[RCF production proofs](hexrcf-production-proofs.md) are retained diagnostics,
not computational scaling or full extension evidence. Companion theorem
applications follow current [Phase 4](../PLAN/Phase4.md) with representative
CI-built proofs and kernel axiom audits. New experiments need a concrete
unresolved decision; none is dispatched by this audit.

## Unresolved requirements and ownership

Current counters are 5 for the Sturm pair, 5 for the OrderedFn pair, 4 for the
SignDet pair and 0 for the RealClosure pair. Available proved APIs do not by
themselves establish the applicable phase obligations.

- **[#10577](https://github.com/kim-em/hex-dev/issues/10577):** closed by merged [#10860](https://github.com/kim-em/hex-dev/pull/10860). All four Sturm/real-algebraic inputs reached Phase 4. The readiness matrix retains computational coverage, finding dispositions, source provenance and practical isolation costs. The Sturm pair reaches Phase 5 through its separate proof acceptance; real-algebraic Phases 5–7 remain outside the eight-library polishing scope.
- **[#10377](https://github.com/kim-em/hex-dev/issues/10377):** closed by merged [#10861](https://github.com/kim-em/hex-dev/pull/10861). Both sign-determination libraries are Phase 4; implementation, correspondence, certificate interfaces, direct examples, independent conformance and retained performance evidence are delivered. Remaining Phases 5–7 belong here. Upstream nested numeral construction is tracked separately by [#10863](https://github.com/kim-em/hex-dev/issues/10863); [#10864](https://github.com/kim-em/hex-dev/pull/10864) reopens the computational RationalFn Phase-4 gate.
- **[#10378](https://github.com/kim-em/hex-dev/issues/10378):** recursive accepted finite-evidence export for joint ordinary-real realization, general compatible incomparable-prefix assembly, full serialization/exploration acceptance and specified conformance/performance evidence. #10665/#10667/#10669 now supply coherent cached gathering, gathered-union identification and validated existing-root reuse; #10755 supplies original number-field integration; #10762 supplies coherent owner readers and `Enlargement.realize`/`realize_model`. Native provider reordering and target-only source reconstruction are proved. The reconciled factories derive canonical owner/cache models and realize complete finite live inventories through one ordinary partial reader. The catalog selector retrieves an installed jointly compatible provider history in any key order, with canonical models and ordinary-real readers derived from a provider model of that installed prefix at the chosen depth. Union arithmetic, order, parent embedding and canonical-owner coherence apply to ordered and reconciled readers through their proved agreement on the shared target base. Reconciled registration, generator coverage and union extension preserve all previous target and owner images; ordered and reconciled gathers agree wherever the ordered owner factory accepts. Canonical reconciled shared/live enlargement, successive frame composition and inherited-provider preservation now use the actual returned models and inclusions. Arbitrary interleaved direct ordinary-real points remain open. The relative inventory route supplies closed data for retained descriptors. The direct recursive `Sample.realizeReplay` theorem, reached arithmetic/zero-packing data and selected-sign inventory assembly from accepted evidence, and subsequent composition of factory models/inclusions with that independent direct theorem remain open. #10780 reconciles retained evidence without promoting Phase 4; tower8 still needs an authoritative input/premise correction.
- **[#10358](https://github.com/kim-em/hex-dev/issues/10358):** generic frontend source certification, frozen context/root/sign/intermediate reconstruction and quotation, reached arithmetic/zero packing and all-live assembly, accepted algebraic progress, general automatic common-field irreducibility certification, and complete nested/successive-infinitesimal joint realization consumption. Merged [#10866](https://github.com/kim-em/hex-dev/pull/10866) covers ordinary-import quotation using one supplied degree-eight irreducibility instance; it does not establish automatic certification. Merged [#10858](https://github.com/kim-em/hex-dev/pull/10858) binds supplied inverse equations to the original operand/source and original divisor guards under a supplied lawful ordinary-real predecessor model. Generic source/model assembly remains open. #10777's original-number-field diagnostics are total and semantically proved, but do not complete frozen quotation. External unshipped prototypes are not merged acceptance evidence. Existing owner regressions and manual examples are reused.
- **[#10575](https://github.com/kim-em/hex-dev/issues/10575):** comprehensive integrated acceptance, the eight libraries' applicable Phases 5–7, remaining owner-safe adapter migration, an agreed optional package boundary, fresh pinned candidate consumers and eligible publication changes. Sturm/OrderedFn API/manual tranches and the SignDet/RealClosure manuals are merged. OrderedFn counters are 5; Phase 6 still requires resolving the API-candidate computational comparison findings and final declaration-review acceptance, including explicit zero-reference dispositions and the import assessment. No owner phase or unrelated distribution eligibility is inferred from these deliverables.

Distribution requirements are separately enumerated in the
[publication plan](real-closure-publication.md), including unreleased phase-1
inputs, rank/real-algebraic Phases 5–7, [#9809](https://github.com/kim-em/hex-dev/issues/9809), mirror bootstrap and full dry run.
