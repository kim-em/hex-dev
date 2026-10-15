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
[SturmTheory](../HexSturmTheory/SPEC/hex-sturm-theory.md).

| Requirement | Actual operation and proof | Tests / independent evidence | Acceptance status |
| --- | --- | --- | --- |
| Shared operation-only polynomial kernels and semantic equality | `DensePoly` and `HexPolyTheory.Interpret`; zero reflection and arithmetic preservation, without injectivity or a field instance on representatives | `HexPoly.InterpretTests`; noncanonical instantiations in sign conformance | Delivered interface; preserve the computation/companion boundary during migration |
| Valid open domains, finite/infinite endpoints, constant heads and refusal | `Sturm.prepare`, `query`, `rootCount`; `HexSturmTheory.Domain`, `query_isSome`, `prepare_isSome` | `conformance/HexSturm`, including endpoint and replay tests | Domain correspondence delivered; [individual declaration review](sturm-declaration-review/README.md) covers the owned production modules. [#10860](https://github.com/kim-em/hex-dev/pull/10860) supplies owner Phase-4 readiness; [proof acceptance](sturm-proof-acceptance.md) records Phases 5–7 |
| Arbitrary certificate soundness and prepared query reuse | `Sturm.check`, `queryPrepared`, `countPrepared`; `Tarski.check_rootSum`, `HexSturmTheory.check_sound`, `queryPrepared_sound`, `countPrepared_sound` | `HexSturmTheoryTests` and `HexQuerySemantics` semantic replay tests; `RealClosureConsumer.Query` checks domain plus value and prepared cardinality | Delivered in the ordinary companion target and public umbrella; caller interpretation/sign laws required |
| Producer acceptance and natural root counts | `certify_checks`, `certifyPrepared_checks`, `rootCount_isSome`, `rootCount_query`, `rootCount_map`, `query_nonneg` | `HexSturmTheory/Tests*`, `adapters/HexSturmTheory/Tests/Replay/Semantics*` and their axiom inventories | Delivered, including combined `query_spec` and positive-clear `rootCount_sturm` from merged #10580; the exact `query_iff` headline from merged [#10660](https://github.com/kim-em/hex-dev/pull/10660) is exposed by the companion umbrella |
| Integer/dyadic agreement after positive denominator clearing | Existing integer `ZPoly.tarskiQuery` and shared Tarski kernel; frontend agreement and domain coverage | `HexRealRoots.TarskiTests`, `HexRealRootsTheory.TarskiTests`; #10580 adds natural-count agreement and semantic guards | Merged #10580 supplies the finite-dyadic agreement; the generic rational frontend retains its infinite endpoints |
| Scaling, comparators, prepared-query memory and attribution | Compiled Sturm/query producers, distinct construction/replay tracks | [Sturm report](hex-sturm-performance.md); [readiness matrix](real-closure-prerequisites.md) and retained source-scoped evidence | Owner Phase-4 attestation merged in [#10860](https://github.com/kim-em/hex-dev/pull/10860); performance limits and historical/inconclusive observations remain explicit |

The shared Tarski proof belongs to
[HexRealRootsTheory.TarskiSoundness](../HexRealRootsTheory/TarskiSoundness.lean).
The frontend domain/producer laws are in
[Domain](../HexSturmTheory/Domain.lean), and root-sum/count semantics in
[Soundness](../HexSturmTheory/Soundness.lean).

## Sign-determination pair

Owning SPECs: [SignDet](../HexSignDet/SPEC/hex-sign-det.md),
[SignDetTheory](../HexSignDetTheory/SPEC/hex-sign-det-theory.md).

| Requirement | Actual operation and proof | Tests / independent evidence | Acceptance status |
| --- | --- | --- | --- |
| Recursive BKR moments, support, retained rank and exact counts | `Reduction.build`, `QueryReduction.build`, tree/system builders; `Reduction.build_checks`, `QueryReduction.check_signs`, `System.retained_rank`, `solveScaled_eq`, `buildTree_complete` | `conformance/HexSignDetTheory`, noncanonical reduction tests; `sign_det_flint.py`, `sign_det_z3.py` | Finite algebra and correspondence delivered; [companion declaration review](sign-det-declaration-review/README.md) covers its 37 production modules without phase promotion; rank producer prerequisite attested by [#10352](https://github.com/kim-em/hex-dev/issues/10352) |
| Root/table producer success from a lawful domain | `Descriptor.build`, `validate`, `buildRoots`; `Descriptor.build_success_formal`, `validate_success_formal`, `buildRoots_success`, `buildRoots_isSome` | `conformance/HexSignDetTheory/Diagnostics/RootSemantics.lean`, `conformance/HexSignDet/FieldChecks.lean`, `RealClosureConsumer.Sign` | Delivered development semantics, not only conditional checker soundness |
| Thom uniqueness, complete coverage and strict order without rational separators | Descriptor full derivative word, `fullOrder`, complete root list; `RawDescriptor.full_unique`, `full_lt`, `Descriptor.buildRoots_roots` | `conformance/HexSignDet/Infinitesimal.lean` (0 and ε in one interval), `FieldChecks.lean`, Z3 infinitesimal oracle | Delivered under an explicit ordered real-closed model, including non-Archimedean fields |
| Selected sign, changed defining polynomial and comparison | `buildSigns`, `signAt`, reencoding and comparison producers; `buildSigns_success`, `signAt_correct`, checked conversion/root preservation | `conformance/HexSignDet/FieldChecks.lean`, `conformance/HexSignDetTheory/Diagnostics/RootSemantics.lean` | Delivered contracts retain embedding/input premises; do not infer joint real realization |
| Shared serialized coefficient evidence, exact contexts and checked cross-level conversion | Integer-only JSON codec, selected-sign records, context-bound proof facts, `HexRealClosure.SignFacts` finite proof assembly and `Dependencies.Graph.decode`/`codec_bytes`/`Decoded.results_bound` | `conformance/HexRealClosureTheory/{DependenciesConformance,PackingConformance,NestedSignsConformance}.lean`, `conformance/HexSignDet/JsonBytes.lean`, byte roundtrip/rejection fixtures; [JSON byte report](sign-det-json-bytes.md); `sign_det_json_bytes.py` | [#10612](https://github.com/kim-em/hex-dev/issues/10612) is merged with its explicit opaque missing-fact boundary. The cross-level envelope supplies typed routing, literal bindings and byte roundtrip laws. Merged [#10758](https://github.com/kim-em/hex-dev/pull/10758) supplies generic coefficient/context reconstruction and paired byte readers with preserved acceptance/refusal. [#10861](https://github.com/kim-em/hex-dev/pull/10861) completes owner implementation, independent conformance and Phase-4 attestation for sign determination. Automatic reached-data assembly for the tower/tactic pipeline remains with their owners |
| BKR/Thom production and replay scaling, height, witness growth and allocation | Actual compiled builders/checkers and matrix operations | [joint](sign-det-joint-performance.md), [height](sign-det-height-model.md), [nested](sign-det-nested-fields.md), [matrix allocations](sign-det-matrix-allocations.md), [height allocations](sign-det-height-allocations.md) | Owner Phase-4 attestation is merged in [#10861](https://github.com/kim-em/hex-dev/pull/10861); retained findings, rejected/inconclusive observations and the retained upstream numeral-construction finding and its repair remain explicit |

Mathematical BKR algebra, selected-root semantics and producer laws are
exposed by the normal [companion](../HexSignDetTheory) and its
`HexSignDetTheory` umbrella. Development availability does not attest owner
performance or publication eligibility. Exact package ownership and remaining
requirements are in the publication proposal.

## Ordered-function pair

Owning SPECs: [OrderedFn](../HexOrderedFn/SPEC/hex-ordered-fn.md),
[OrderedFnTheory](../HexOrderedFnTheory/SPEC/hex-ordered-fn-theory.md).

| Requirement | Actual operation and proof | Tests / independent evidence | Acceptance status |
| --- | --- | --- | --- |
| Exact approximations and successful finite signs | `Real.enclose`, `finiteAttempt`, `sign?`, `approxAttempt`; `enclose_sound`, `finiteAttempt_sound`, `sign?_sound`, width/containment theorems | `HexOrderedFnTheory.Tests`, `LiouvilleTests`, `conformance/HexOrderedFn`; `ordered_fn_real.py` | Delivered; finite success needs certified containment and denominator nonvanishing |
| Total signs and approximation search for caller-supplied constants | `Real.sign`, `approx`, registered `Extension`; `attempt_progress`, `sign_acc`, `approx_acc`, `Extension.sign_eq`, `compare_eq` | Compiled Liouville integration; original divisor and wrong-subject tests | Delivered conditional on relative transcendence over the entire predecessor field plus source containment/width laws; no bundled π/e provider |
| Infinitesimal positivity, comparisons, successive levels and ordered coefficient transport | `Infinitesimal.sign`, `compare`, `RationalFn.map`; Hahn `embed`, `X_pos`, `X_lt_C`, `X_lt_pow`, `mapHom_sign`, `mapHom_strictMono` | `InfinitesimalTests`, corrected Example-3 factor identity; `ordered_fn_z3.py`; new ordinary umbrella consumer | Delivered; the new consumer consumes order laws, not a nonstandard-analysis tactic |
| Computational Phase 4 and companion proof policy | Scan, arithmetic, Horner, real refinement, two-/three-level approximation families | [OrderedFn report](hex-ordered-fn-performance.md), retained raw data, Z3/FLINT ratios and representative profiles | [#10376](https://github.com/kim-em/hex-dev/issues/10376) complete; the original Phase-4 report has no concerns; the public API tranche [#10750](https://github.com/kim-em/hex-dev/pull/10750) completed Phase 5. The companion’s independent proof/API and manual acceptance is merged in [#10928](https://github.com/kim-em/hex-dev/pull/10928), with HexOrderedFnTheory at 7. HexOrderedFn remains at 5: the subsequent [API review](hex-ordered-fn-api.md) retains four flagged computational regressions under the declared rule; no further unchanged comparison is permitted. The core’s share of the 49 API dispositions and its import assessment are merged in [#10935](https://github.com/kim-em/hex-dev/pull/10935); its performance findings still prevent final Phase-6 acceptance. Tower clean/eager evidence is a distinct [#10378](https://github.com/kim-em/hex-dev/issues/10378) obligation |

The actual public umbrella is
[HexOrderedFnTheory](../HexOrderedFnTheory.lean). Caller approximation
laws justify interpreted computation; successful finite examples without
transcendence do not prove total sign search for arbitrary providers.

## Real-closure pair and integrated path

Owning SPECs: [RealClosure](../SPEC/Libraries/hex-real-closure.md),
[RealClosureTheory](../SPEC/Libraries/hex-real-closure-theory.md).

| Requirement | Actual operation and proof | Tests / independent evidence | Acceptance status |
| --- | --- | --- | --- |
| Canonical zero with noncanonical nonzero storage, selected reducible roots | `Algebraic.Element.ofPoly`, zero/sign, local cofactor inversion; `denote_eq_zero`, `denote_ofPoly`, `cofactor_spec`, arithmetic/sign correspondence | `HexRealClosure.Tests`, `QAdjoinTests`, selected-root conformance | Delivered slice; no field instance on raw quotient representatives |
| Clean monic retention, non-monic/raw policy and value preservation | `Context.reduce`, `queryPoly`, element packing; `evalPoly_reduce`, clean companion laws, `reduce_nonmonic`, `reduce_unclean` | Algebraic tests and non-monic isolation fixtures | Delivered policies; do not treat scaled pseudo-remainders as value-preserving remainders |
| Yun decomposition, zero/all, constants, termination, multiplicities and order | `Roots.roots`, `Context.roots`, `roots?`; `Roots.roots_success`, `Context.roots_all`, `roots?_success`, `roots_spec`, `roots_sorted` | `RootFactorsTests`, `TowerRootsTests`; `real_closure_deflation.py`, `real_closure_isolation.py`; new `RealClosureConsumer.Tower` | Delivered under a common model; consumer composes success and exact multiplicities without assuming successful output |
| Root extensions, coefficient embeddings and stored native values | `Context.adjoin`, `Root.embed`, root materialization; `Model.adjoin_embed`, `Root.embed_value`, `convertedValue_value`, `signAt_value` | `TowerModelTests`, `TowerRootsTests`, isolation oracle | Delivered selected embeddings, separate from joint ordinary-real realization |
| Persistent refinement, all requested live dependency closure and general enlargement | Context/refinement/conversion APIs; `TowerTransport`, rebuilt suffix model and selected-root preservation | `TowerTransportTests`, `TowerRefinementTests`, changed-context rejection | Merged [#10651](https://github.com/kim-em/hex-dev/pull/10651)/[#10654](https://github.com/kim-em/hex-dev/pull/10654)/[#10655](https://github.com/kim-em/hex-dev/pull/10655) supply shared owner maps, real-prefix inclusions and ambient/base models. `Shared.enlarge?_models` preserves all original values assuming coherent `Inclusions.Models`; merged [#10662](https://github.com/kim-em/hex-dev/pull/10662) derives source/base owner models from a compatible target provider history through `BaseInclusion.Model.derive`, preserving the supplied target model. Merged [#10665](https://github.com/kim-em/hex-dev/pull/10665) supplies coherent gathering/cached rebuilds. Merged [#10762](https://github.com/kim-em/hex-dev/pull/10762) supplies `Tower.Shared.realize_values` through retained checked inclusions, actual gather success and a supplied base realization, constructing its symbolic reference internally; native provider reordering and `BaseReconciliation.Model.deriveCanonical` derive source realizations/models from the target alone; canonical owner lookup, cache consumers and joint target selection are integrated through the reconciled factories and validated-prefix catalog; canonical shared/live enlargement preserves these owners and caches through successive predecessor maps, with ordinary finite-inventory realization; assembly of a missing joint provider history remains open |
| New infinitesimal below all transported positive old values | `Context.enlargeWithParameter?`; `enlargeWithParameter?_model`, `_ordered`, `_algebraic` | `TowerEnlargeOrderTests`: successive square roots, old inverse/gaps and preceding infinitesimal | Delivered for the actual returned conversion; not total all-live enlargement |
| Compatible algebraic union and real-closedness | `Union`, `TowerUnion`, relative ambient model; union real-closedness and common extension | `UnionTests`, `TowerModelTests` | Native finite `Presentation` quotient bijection, algebra equivalence and real-closedness merged in [#10616](https://github.com/kim-em/hex-dev/pull/10616); gathered-union identification in [#10667](https://github.com/kim-em/hex-dev/pull/10667) is merged |
| Sections/sectors, original-model signs and joint ordinary-real realization | Complete root families and sample/sector contracts | Native sample API and exact sample families from merged [#10607](https://github.com/kim-em/hex-dev/pull/10607); `Specialize.realizeReplay` for one rational-function infinitesimal step | Local section/sector coverage, actual interpretation and sector sign constancy delivered. One-step realization assumes an ordered real embedding of the base; merged [#10888](https://github.com/kim-em/hex-dev/pull/10888) adds finite native reconstruction from retained owners and a validated infinitesimal base, with dependency discovery before witnesses and checked requested propositions/guards. Its `KernelReplay.NativeAssemblyUse.coordinate` consumer derives the original root equation and coefficient-zero addition equation at one returned interpretation/coordinate. General interleaved normalization, simultaneous realization and a successful multilevel native fixture remain with #10378 |
| Independent trivial-base fast path agreement | `Trivial.Rational.roots`; `Trivial.Rational.roots_eq`, `compare_eq` | `TrivialTests`, real-algebraic root/multiplicity/order conformance | Full native rational tower conversion, root/multiplicity/order, arithmetic and inverse agreement merged in [#10624](https://github.com/kim-em/hex-dev/pull/10624) with independent FLINT cases; merged [#10755](https://github.com/kim-em/hex-dev/pull/10755) retains original selected number-field coordinates through roots and samples. Broader registered-base coverage and the final evidence audit remain with #10378 |
| Reconstructible printing, registered constants and exploration/number-field integration | Base/context/element codecs, `FrameFormat`; `read_write`, `read_stale`, exact registry/signature bindings | `CodecTests`, `BaseCatalogTests`, `FrameFormatTests`; nested read/replay fixtures | Codec slices and original number-field integration (#10755) are delivered. The test-only [#10914](https://github.com/kim-em/hex-dev/pull/10914) fixture uses the existing Liouville test provider to reconstruct six packed/indexed expressions after algebraic enlargement over a second infinitesimal. Its [checks](../HexRealClosureTheory/ReprProviderTests.lean) observe element/coefficient signs and eight missing/changed-version refusals for the four packed kinds; indexed root/root-set cases check text roundtrip. This evidence is separate from joint ordinary-real realization. Complete serialization/exploration acceptance and the final evidence audit remain with [#10378](https://github.com/kim-em/hex-dev/issues/10378). Registry names must resolve to the same caller-supplied source |
| Nested evidence and adversarial cases | Actual α²=2+ε₁, β²=α+ε₂ selected-sign fixture; selected inversion, shared prepared domain and literal context checks | `conformance/HexRealClosure/NestedReplay.lean`; changed consumers, cycles, stale contexts and zero/wrong denominators; isolation oracle | Functional evidence merged in [#10610](https://github.com/kim-em/hex-dev/issues/10610); no joint-realization or computational scaling attestation |
| Corrected paper Example 3, tower8, MetiTarski, Rioboo/Strzeboński, clean/eager and representative attribution | Ordinary native tower/root algorithms | [arithmetic experiments](hex-real-closure/general-arithmetic.md), [isolation anchors](hex-real-closure/isolation-anchors.md), [storage experiment](real-closure-storage-experiments.md), owner conformance | The [Phase-4 report](real-closure-phase4.md) indexes retained clean/eager and MetiTarski evidence, including inconclusive results and remaining obligations. The [original source archive](bench-results/real-closure-cade24-inputs/README.md), recovered in merged [#10899](https://github.com/kim-em/hex-dev/pull/10899), supplies `basic.py`/`nlsat.py` provenance and resolves the tower8 coefficient/premise discrepancy: executed stage degrees are 4, 2, 4, 5, 5, the first constant is `4 − 2ε²`, and the third executed polynomial has degree four despite its label. Native and exact Z3 conformance cover the original [Rioboo](real-closure-rioboo.md) and real [Strzeboński](real-closure-strz.md) inputs. Tower8 execution and matched clean/eager outcomes require caller constant inputs; the unsupported-case versus required tower8 evidence decision remains open with #10378 below. Required counters, certificate-sharing/depth costs, remaining trivial-path families and the final audit are still required. Owner Phase-4 attestation remains open; functional and provenance checks do not replace it |

The consumer supplies a `Tower.Model` explicitly. Model existence and transport
are separate theorems; a model over a non-Archimedean real closed field does
not itself produce ordinary-real values for nested infinitesimal samples.
The consumer contains no new algorithm or replacement for the owner's API
examples. Complete end-to-end constant → infinitesimal → algebraic extension
→ enlargement → reconstructible printing → ordinary-real tactic acceptance
remains open across these rows.

The finite ordinary-real consumer boundary is concrete:
[`Transport.Finite.DescriptorData`](../adapters/HexRealClosureTheory/TransportDescriptor.lean)
and [`Transport.Finite.ReplayData`](../adapters/HexRealClosureTheory/TransportReplay.lean)
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
[`Transport.Inventory.descriptor_data`](../adapters/HexRealClosureTheory/TransportInventory.lean)
produces closed `Transport.DescriptorData`. Refreshed target-side descriptors
additionally require `Collection.inventory` as `extra`, or as `fresh` after an
enlargement. The owner's
[`collection_replay`, `enlargement_replay` and `target_replay`](../adapters/HexRealClosureTheory/SharedRealizationTests.lean)
exercise these closed-data cases; `target_replay` explicitly passes that extra
inventory, and `enlargement_replay` covers original-owner descriptors.

Selected-sign replay machinery is also delivered: `Inventory.replay_data` and
`Finite.ReplayData.of_closed` supply the corresponding data when given agreement
for `Inventory.replay raw.head raw.lower raw.upper (raw.queries ++ qs) signs.evidence`.
That inventory must be requested through `extra`/`fresh`, or assembled by the
exporter; a frame does not store selected-sign records.
[`TransportFiniteTests.identity_point`](../adapters/HexRealClosureTheory/TransportFiniteTests.lean)
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
| Real-algebraic/Sturm prerequisites | Existing `compare_eq`, real root completeness/multiplicity/order, query/root-count semantics | [#10860](https://github.com/kim-em/hex-dev/pull/10860) completes owner Phase-4 readiness for all four inputs. The query/root-count and real-algebraic root completeness/multiplicity/order APIs are proved. [Sturm proof acceptance](sturm-proof-acceptance.md) records Phase 7 for both Sturm libraries; real-algebraic Phases 5–7 remain separate distribution work |

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

## Supplied root tables and complete cells

Merged [#10907](https://github.com/kim-em/hex-dev/pull/10907) exports complete
root lists from accepted full derivative replay through
`RootReplay.Result.coverage` and `ordered` in any lawful real-closed parent
model. These wrappers reuse `Descriptor.rootsFrom_coverage` and
`rootsFrom_ordered` from [#10903](https://github.com/kim-em/hex-dev/pull/10903).
The finite quotation fixtures use a fixed positive-√2 parent and one ordinary
selected point. They retain original divisors for zero and nonzero quotients and
check supplied inverse equations, without assuming equality to a native
inverse. The dictionaries remain kernel-assembly interfaces, rather than a
strict compiled checker for arbitrary packets. See the
[guarded matrix report](hexrcf-guarded-matrix.md).

Merged [#10912](https://github.com/kim-em/hex-dev/pull/10912) checks complete
supplied section/sector matrices through `CellReplay.check`.
`check_domains` proves the original divisor conditions for any successful
verdict; `check_sound` proves the shared one-quantifier formula at the interpreted values from
`.ok true`, a whole-line `RootReplay.Result` for the radical core, and a
supplied lawful ordinary-real parent model. An accepted `false` is diagnostic
and proves no negation. The checker derives root coverage, cell membership
and sign constancy from checked data; those conclusions are not supplied as
semantic certificate fields. `CellRead` preflights original guards before
decoding, while `CellReplay.check` checks guards before radical identities.
Quotation checks the source formula, fixed coefficient valuation, divisor count
and ordered divisor identities afresh.

The [cell replay report](hexrcf-cell-replay.md) retains the rational-coefficient
fixture: two root sections, three open sectors, repeated and zero atoms,
strict finite boundaries, an accepted empty-root case and boundary refusal controls. This is
accepted supplied-cell quotation, not general algebraic production, complete
source/provider history assembly or strict replay for missing predecessors.
The implementation and its manual examples remain owned by #10358.
The owning [RCF SPEC](../HexRCF/SPEC/hex-rcf.md) and the earlier
[root replay](hexrcf-root-replay.md) and
[nested replay](hexrcf-nested-root-replay.md) reports still describe supplied
coverage/order exports as missing. Updating those passages to match the merged
APIs, and documenting the supplied-cell boundary, remains an explicit #10358
documentation requirement; this audit does not replace the owning contract.

## Finite native reconstruction

Merged [#10888](https://github.com/kim-em/hex-dev/pull/10888), source
`c5bd4afdad`, supplies the semantic development modules `FiniteConditions`,
`FiniteReconstruction`, `NativeFactory`, `NativeAssembly` and their checked
readers. Native evaluation provides literal graph/polynomial data; independent
replay records and strict coefficient codecs supply kernel-checked meaning.
Owner, depth, operand and record kind identify cache entries, and environment rollback
also restores the cache. Fuel bounds dependency discovery; exhausted or absent
evidence is an error rather than an accepted condition.

The CI-built experiment consumer
[`KernelReplay.NativeAssemblyUse`](../experiments/KernelReplay/NativeAssemblyUse.lean)
reuses the staged fixture's exported `statement`/`exists_joint` through a public
import, without `import all` in this consumer. The staged producer fixture itself
uses `import all`; its one sealed import, `HexSturm.Basic`, has an exact
entry in the `check_dag.py` allowlist. The consumer destructures both existential
witnesses and all eleven conjuncts, deriving the original root equation and
coefficient-zero addition at the same returned interpretation and coordinate.
Its context proofs retain the original descriptor and the actual adjoined
context. This supplies a mathematical consumer rather than an acceptance claim
based only on native example output. CI names 32 `KernelReplay` module targets,
19 of them added by #10888. A twentieth new module, `FiniteThomWitness`, builds
as a dependency of `FiniteThomJoint`; CI also names two existing replay executables.
Build-time controls reject exhausted discovery, missing owners and
wrong-polynomial callbacks; the consumer has standard-three axiom guards.
The 15 controls in [`run.py`](../experiments/KernelReplay/run.py) predate #10888
and drive the existing `hexsigndet_kernel_replay_probe`: root, fact-operation,
nested, generated and collection probes; emission and byte replay of the
serialized SignDet graph, including count and context mutations; and argument
handling. None invokes the #10888 native reconstruction path.

The exercised path still does not establish general dependency-closed
interleaved normalization, successful multilevel native joint reconstruction or
the remaining specified conformance/performance evidence. Directly computed
coefficient operands and product-law requests have no successful end-to-end
fixture: the owning SPEC records dependency traversal exceeding the local
8 GiB experiment limit. This is a retained resource limitation, not a scaling
pass. Merged [#10899](https://github.com/kim-em/hex-dev/pull/10899) resolves
the original `tower8` source and premise correction through the
[verified CADE-24 input inventory](bench-results/real-closure-cade24-inputs/README.md).
The first executed polynomial is reducible, with constant `4 − 2ε²`;
the retained no-root finding applies to the paper's different printed quartic.
The third executed polynomial is degree four, despite the degree-five label.
The source inventory verifies all five root-selection indices and identical
clean/eager script actions apart from the historical normalization setting;
it establishes neither Hex execution nor matching semantic outcomes.
Original workload execution, stage measurements, counters and matched storage
comparisons remain with #10378 when the caller constant inputs are supplied. Ports must preserve the recorded root-index-zero
selections and verify the returned ordering against the pinned Z3 oracle;
source verification alone does not establish root ordering or selected values.
The retained metadata links the paper/example release to the archived payload,
but the download-number/file-UUID association is inferred rather than directly
recorded. Earlier no-root and input-obstruction reports retain their stated
paper-transcription scope.

The original `tower8` registers π and e before ε and the algebraic roots.
Although π first occurs in the coefficients of `r3` and e in those of `r4`,
the whole tower is constructed over `ℚ(π)(e)`. Its initial context already needs
the caller approximation procedures and effective progress/relative-transcendence
assumptions specified by the [constant contract](../SPEC/Libraries/hex-real-closure.md#exploration-and-downstream-integration).
Separate transcendence results would not justify transcendence of e over
`ℚ(π)`. These are conditional caller inputs, not provider-production or
transcendence-proof obligations of this family. When the required inputs are
unavailable, record the original workload as unsupported. Running `r0`–`r2`
over `ℚ(ε)` instead is a separate reduced case with a different coefficient
field and sign path; it is not stage evidence for the original workload and
cannot be extended by inserting π and e below the existing infinitesimal.
Bounded certified sign attempts cannot replace the total tower coefficient field.
This integration scope adds no bundled π/e providers.

An owner SPEC decision remains open on #10378: core conformance requires
“`tower8` over infinitesimals” and Phase 4 requires its isolation and matched
clean/eager evidence, while the same SPEC allows unsupported-case records when
caller constant inputs are absent. Without those inputs, the original workload
cannot supply the required execution evidence. The owner must clarify whether
an unsupported record discharges that requirement and which infinitesimal-only
fixture, if any, fulfills the core requirement. This report accepts neither a
reduced variant nor an unsupported record as a Phase-4 pass. The owning
Phase-4 report's remaining-scope row lists caller inputs to supply; this is a
conditional workload input, not a requirement to develop providers or prove
relative transcendence within #10378. Revise the owning SPEC before implementing
any changed acceptance contract.

These semantic sources live under `adapters/`. #10888 also adds Mathlib-free
record/query readers and packet modules to the computational umbrella, which
remains Mathlib-free. Listing the adapter modules as explicit roots of the development
`HexQuerySemantics` library, and the `KernelReplay` consumer targets, do not
make them published companion imports.
Companion migration, pinned package requirements and candidate downstream
consumers remain in the [publication plan](real-closure-publication.md).

## Additional merged adapter and evidence milestones

Merged [#10922](https://github.com/kim-em/hex-dev/pull/10922) supplies
[complete frozen cells over a fixed algebraic parent](hexrcf-algebraic-cells.md).
For `p(X) = X² − √2` over the selected positive embedding of ℚ(√2),
the matrix `p(x) ≥ 0 ∧ p(x) ≤ 0 ∧ 0 = 0` has two section rows and three
sector packets. Ordinary-kernel replay consumes the
supplied scalar inventory, checks radical identities and quotes the original
real existential. The original `0 / (−1)` guard remains required after numerator
normalization; zero-divisor preflight precedes malformed decoding. Wrong
subjects, contexts, boundaries and samples have explicit refusal controls.
This is available supplied-evidence integration, with a HexRCF manual chapter and
proof examples that reuse the owner’s proved interfaces. General construction completeness and arbitrary missing-record
compiled replay remain outside that milestone; its native arithmetic fallback
is not evidence of a strict general checker.

Merged [#10923](https://github.com/kim-em/hex-dev/pull/10923) strengthens finite
base lookup: equality checks preserve the caller’s interpreter and reader
metavariables. Candidate natural casts must match the complete guarded
proposition definitionally. Closed agreements become kernel-checked theorems;
open agreements retain their hypotheses for the enclosing kernel check.
The new BaseLookup controls reject foreign or unspecified interpretations
without assigning caller metavariables. They also cover symbolic/computed
natural casts, definitional aliases and missing retained leading evidence.
A shared expression with 48 arithmetic layers is refused within the heartbeat limit;
it is not an acceptance example. These are finite evidence-reader contracts,
not automatic all-live assembly or general joint ordinary-real realization.

Merged [#10921](https://github.com/kim-em/hex-dev/pull/10921) retains
[native MetiTarski producer counters](bench-results/real-closure-metitarski-counts/README.md).
Its untimed instrumented commands agree with the ordinary packets at the four
recorded degrees. The report distinguishes outer entry counts from lower-field
arithmetic and overlapping counters. These data neither resolve the earlier
inconclusive timing model nor attest the tower’s Phase 4. Archive verification
and mutation controls check the retained evidence; no repeated timing collection
is needed for this requirements update.

## Unresolved requirements and ownership

Current counters are 7 for both Sturm libraries, 5 for
HexOrderedFn and 7 for HexOrderedFnTheory, 5 for HexSignDet and 7 for
HexSignDetTheory, and 0 for
the RealClosure pair. Available proved APIs do not by
themselves establish the applicable phase obligations.

- **[#10577](https://github.com/kim-em/hex-dev/issues/10577):** closed by merged [#10860](https://github.com/kim-em/hex-dev/pull/10860). All four Sturm/real-algebraic inputs reached Phase 4. The readiness matrix retains computational coverage, finding dispositions, source provenance and practical isolation costs. The [direct Sturm oracle](sturm-direct-conformance/README.md) supplies the owning SPECs' rational selected-root sign fixtures without treating inherited integer tests as independent frontend coverage. The Sturm [proof acceptance](sturm-proof-acceptance.md) records Phases 5–7 for both libraries, using the [individual API/manual assessment](sturm-declaration-review/README.md) and complete native comparison; real-algebraic Phases 5–7 remain outside the eight-library polishing scope.
- **[#10377](https://github.com/kim-em/hex-dev/issues/10377):** closed by merged [#10861](https://github.com/kim-em/hex-dev/pull/10861). Both sign-determination libraries completed owner Phase 4; implementation, correspondence, certificate interfaces, direct examples, independent conformance and retained performance evidence are delivered. Their [proof acceptance](sign-det-proof-acceptance.md) records Phase 5. SignDet Phases 6–7 belong to #10575.
- **[#10378](https://github.com/kim-em/hex-dev/issues/10378):** general dependency-closed interleaved normalization and simultaneous ordinary-real realization; joint targets for incomparable real-key prefixes; the general direct `Sample.realizeReplay` theorem and composition with factory models/inclusions; automatic reached arithmetic, zero-packing and selected-sign inventory assembly; direct computed operand/product-law requests; successful multilevel native joint reconstruction; full serialization/exploration and specified conformance/performance evidence and acceptance. The finite reconstruction section supplies usable merged contracts; #10914 supplies native test evidence through the existing catalog APIs. The original CADE `tower8` and clean/eager obligations remain conditional on caller π/e procedures and laws; the required-evidence versus unsupported-case decision remains open. Neither reduced inputs nor reconstructed paper sources attest Phase 4.
- **[#10358](https://github.com/kim-em/hex-dev/issues/10358):** generic frontend source/provider/history certification, reached-data and all-live assembly, accepted general algebraic production and completeness, automatic common-field irreducibility certification, and complete consumption of nested/successive-infinitesimal joint realization. Supplied full root-table, inverse/divisor and complete-cell quotation contracts from #10907/#10912, and the fixed algebraic-parent cell replay from merged #10922, are available now, as described above. They use explicit lawful-model and accepted-evidence hypotheses; they do not close general production or missing-predecessor replay. The [#10858](https://github.com/kim-em/hex-dev/pull/10858) supplied inverse contract binds the original operand/source and divisor guards under a supplied lawful ordinary-real predecessor model. The [#10867](https://github.com/kim-em/hex-dev/pull/10867) `NativeFormula` evaluator is not identified with `Samples.run` or `Tower.Sample.signs`, and frozen context/history/reached-data assembly into the tactic path remains incomplete. `NativeSamples.row_converted` separately connects sample signs to `NativeSpecialize.row`; full native/infinitesimal root coverage remains open. Reconcile the owning RCF SPEC and root-replay report passages with the merged coverage/order and cell interfaces. External unshipped prototypes are not merged acceptance evidence. Reuse the owner's existing API/manual examples.
- **[#10575](https://github.com/kim-em/hex-dev/issues/10575):** final integrated acceptance, all applicable Phase 5–7 exit criteria for the eight family libraries, including proof/API quality, docstrings, native computation and Lean-checked construction claims, manuals/READMEs and rendered-page inspection, owner-safe semantic adapter migration and integration, an agreed optional package boundary, fresh pinned candidate consumers and eligible publication preparation. Both Sturm libraries record Phase 7. OrderedFn records core Phase 5 and companion Phase 7. SignDet records core Phase 5 and companion Phase 7. Its [serialization review](sign-det-declaration-review/core-serialization.md) is merged in [#10913](https://github.com/kim-em/hex-dev/pull/10913). Parser review [#10915](https://github.com/kim-em/hex-dev/pull/10915), compiler/lint evidence [#10917](https://github.com/kim-em/hex-dev/pull/10917), independent companion acceptance [#10930](https://github.com/kim-em/hex-dev/pull/10930) and core-use assessment [#10931](https://github.com/kim-em/hex-dev/pull/10931) are merged; the companion records Phase 7 while the core still needs its computational comparison. The RationalFn repair is merged in [#10871](https://github.com/kim-em/hex-dev/pull/10871), closing [#10863](https://github.com/kim-em/hex-dev/issues/10863) and restoring HexRationalFn to 4; HexRationalFnTheory was not rolled back. The [nested-sign report](sign-det-nested-signs.md) retains the pre-repair constructor-cost finding that motivated the rollback; the [constant-construction report](rationalfn-constants.md) retains the repair comparisons. This does not discharge OrderedFn's separate API-candidate comparison findings for the computational library. The companion’s [independent acceptance](ordered-fn-declaration-review/theory-acceptance.md) adopts its individual public-API decisions and current import/kernel/manual checks; this does not resolve the core’s four flagged regressions under the declared rule in the [retained follow-up](bench-results/ordered-fn-regression-followup/README.md); no further unchanged comparison is permitted. The core’s share of the 49 API dispositions and its import assessment are merged in [#10935](https://github.com/kim-em/hex-dev/pull/10935); its performance findings still prevent final Phase-6 acceptance. Sturm’s [complete native comparison](bench-results/sturm-phase6-comparison/cap-complete-v3/README.md) passes all 58 families and four balanced blocks under the reviewed cap adaptation. Its original failed capture and consumed reservation remain retained. The [final acceptance](sturm-proof-acceptance.md) combines that result with the unchanged core’s individual API decisions and current lint, import, kernel, conformance and manual checks. SignDet’s final computational baseline comparison and API/use acceptance remain separate from source assessments and lints. Current reference/use, import, lint and applicable computational regression checks remain part of final acceptance. No unrelated dependency or distribution phase is inferred from these deliveries.

Distribution requirements are separately enumerated in the
[publication plan](real-closure-publication.md), including unreleased phase-1
inputs, rank/real-algebraic Phases 5–7, [#9809](https://github.com/kim-em/hex-dev/issues/9809), mirror bootstrap and full dry run.
