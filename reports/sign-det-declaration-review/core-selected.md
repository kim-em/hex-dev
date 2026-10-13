# Selected-root query signs

This assessment covers the 19 named declarations and three structure fields in
`HexSignDet/SelectedSigns.lean`. The [bindings](core-selected-manifest.json)
identify the reviewed source and the proof clients changed to use its acceptance
API. This is partial computational review; it does not complete Phase 6 or
replace the owner's remaining supplied-root-list semantic exports.

## Declaration assessment

| Declaration | Assessment |
| --- | --- |
| `RawDescriptor.checkSigns` | Requires descriptor shape, literal context, complete joint replay and exactly one filtered count-one row. All additional queries participate in the replay; a matching row alone is insufficient. |
| `RawDescriptor.checkSigns_eq` | Characterizes all four guards in both directions for arbitrary supplied evidence. Arguments are implicit so clients can use `.mp` and `.mpr` directly; this is an acceptance theorem, not root semantics. |
| `Descriptor.checkSigns` | Delegates to the same raw checker on the validated descriptor, preserving the supplied vector and replay. |
| `Descriptor.checkSigns_eq` | Uses the descriptor's existing shape/context proof and exposes both remaining obligations. It retains the full joint query list and singleton row. |
| `SelectedSigns` | Stores the ordered vector, exact replay and proof binding both to the descriptor and queries. Each field is documented. No default or inferred sign substitutes for supplied evidence. |
| `SelectedSigns.value` | The singleton-query type supplies a valid index, so extraction has no missing-entry fallback. |
| `SelectedSigns.check_eq` | Extracts the complete validated table and filtered row through the named acceptance API and `Replay.table_rows`, without unfolding either representation. |
| `SelectedSigns.ternary` | Table invariants force every additional coordinate to be a ternary code; this does not assume semantic correctness of the sign function. |
| `SelectedSigns.count` | Accepted replay plus well-formed finite observations and moment interpretation gives exactly one occurrence of the full word. The interpretation hypotheses are essential. |
| `SelectedSigns.signs_of_count` | Exact counts for every word exclude additional matching observations. Positive table membership and the singleton filter identify the supplied signs. A single positive row without count completeness would not suffice. |
| `SelectedSigns.signs_eq` | Derives those complete counts from finite observation interpretation. The companion separately supplies root-set interpretation. |
| `Descriptor.buildSignsPrepared` | Retains producer diagnostics, filters the complete table, checks count one and vector length, and finally reruns the independent selected checker. Arbitrary supplied preparations do not imply success. |
| `Descriptor.buildSigns` | Uses the descriptor's actual shared preparation. Preparation failure remains an internal diagnostic here; lawful-domain producer success is proved in the companion. |
| `Descriptor.buildSigns_prepared` | Identifies cached preparation with the ordinary producer only when the supplied domain is exactly the successful preparation result. |
| `Descriptor.buildSigns_domain` | Successful construction implies actual successful preparation, without assuming arbitrary operations satisfy field laws. |
| `Descriptor.buildSigns_ofTable` | A successful actual prepared replay and exact extending count-one row discharge the remaining constructor guards. Preparation bindings, descriptor width and vector conversion are explicit. |
| `Descriptor.signAt` | Returns the successful singleton result; its diagnostic panic branch is excluded by the companion's lawful-interpretation producer proof. The `Except` interface exposes internal failures for arbitrary operations. |
| `Descriptor.signAt_ofBuild` | Characterizes the accessor using the actual successful construction equation. It neither assumes nor establishes unconditional producer success. |
| `Descriptor.signAt_ternary` | Successful values are ternary by table invariants. Lean's diagnostic default branch is also zero; this representation fact alone gives no selected-root semantics. |

## Clients and verification

The existing selected-table constructor and prepared producer proof use the
reverse characterization. Graph replay/encoding agreement uses the same API
for acceptance and rejection. Finite transport and coefficient substitution
use its forward and reverse directions, retaining every domain, derivative,
context and complete-replay premise. Computational definitions and guards are
unchanged; only proof bodies and documentation change.

The existing `selected_kernel` conformance fixture checks acceptance, an
incorrect sign and a stale context with the ordinary kernel. Its derivative
fixtures additionally exercise copied query evidence. New axiom guards for
both characterizations require exactly `propext`, `Classical.choice` and
`Quot.sound`. Validation includes the complete monorepo build, the changed
graph/transport/substitution clients, conformance, import DAG and admission
scan. These checks are not computational performance measurements.

The binding checker verifies named declaration inventory and exact source
bytes. It does not mechanically establish the mathematical assessment, field
documentation, all compiler-generated constants or whole-repository usage.
Other computational modules still require separate assessment and Phase-6
acceptance; the companion's root-semantics and producer-success proofs remain
distinct from this finite acceptance API.
