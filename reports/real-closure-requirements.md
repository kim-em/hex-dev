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
| Shared serialized coefficient evidence, exact contexts and checked cross-level conversion | Integer-only JSON codec, selected-sign records, context-bound proof facts, `HexRealClosure.SignFacts` finite proof assembly and `Dependencies.Graph.decode`/`codec_bytes`/`Decoded.results_bound` | `DependenciesConformance`, `GraphSignsConformance`, `PackingConformance`, `NestedSignsConformance`, byte roundtrip/rejection fixtures; [JSON byte report](sign-det-json-bytes.md); `sign_det_json_bytes.py` | [#10612](https://github.com/kim-em/hex-dev/issues/10612) is merged with its explicit opaque missing-fact boundary. The cross-level envelope supplies typed routing, literal bindings and byte roundtrip laws. [#10377](https://github.com/kim-em/hex-dev/issues/10377) still owns automatic intermediate coefficient evidence, context reconstruction and strict compiled arithmetic replay |
