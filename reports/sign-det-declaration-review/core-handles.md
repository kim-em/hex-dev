# Prepared query handles and equal-operation transport

This assessment covers 25 named declarations in `QueryHandle`,
`DescriptorOperations` and `HandleOperations`, and both query-handle fields.
It is partial core review, with no phase or performance attestation.
A prepared domain belongs to an exact validated descriptor and sign function;
equal operation dictionaries permit proof transport rather than a change to
mathematical interpretation.

| Declaration | Assessment |
| --- | --- |
| `QueryHandle` | Private construction retains the exact prepared domain and its preparation equation, indexed by the complete descriptor. A handle does not cache query answers. |
| `QueryHandle.ofChecked` | Restores a handle only from the actual preparation equation on the descriptor's original head and endpoints. |
| `QueryHandle.ofChecked_domain` | Exposes literal domain preservation without requiring callers to unfold the constructor. |
| `QueryHandle.ofChecked_eq` | Reassembling the same handle preserves the complete value; proof fields agree by proof irrelevance. |
| `QueryHandle.ofChecked_heq` | Equal descriptor indices give heterogeneous equality of the restored handles; semantic equality of roots alone is insufficient. |
| `Descriptor.prepareQueries` | Calls preparation once and returns absence when that actual call fails; arbitrary coefficient operations have no unconditional success guarantee. |
| `Descriptor.prepareQueries_eq` | Given the actual successful preparation equation, identifies the exact returned canonical handle. |
| `Descriptor.prepareQueries_isSome` | Characterizes handle existence by actual preparation success, in both directions, without running selected-query production. |
| `QueryHandle.map_heq` | Mapping optional cached handles preserves their complete value only under equal descriptor indices and a pointwise heterogeneous-equality hypothesis. |
| `Descriptor.prepareQueries_heq` | Literal equal descriptor indices preserve the optional preparation result; no chosen semantic embedding is substituted. |
| `QueryHandle.bindings` | Recovers the original sign operation, head and both endpoints from the actual preparation equation. |
| `QueryHandle.buildSigns` | Reuses the prepared domain but rebuilds joint query evidence for the caller's exact ordered queries. |
| `QueryHandle.buildSigns_eq` | Proves exact agreement with the ordinary selected-sign producer, retaining both success and internal errors. |
| `QueryHandle.checkSigns` | Checks arbitrary supplied evidence against the original validated descriptor; stored domain data do not replace that checker. |
| `QueryHandle.checkSigns_eq` | Exposes the exact checker identity for any handle and supplied query/vector/replay, without semantic or producer premises. |
| `QueryHandle.signAt` | Uses actual singleton-query production and the existing diagnostic zero fallback on internal failure. Correct mathematical signs require companion laws excluding failure. |
| `QueryHandle.signAt_eq` | Preserves the ordinary singleton wrapper result in both success and error branches. |
| `Descriptor.prepareQueries_ofBuild` | Actual successful selected-query production gives a preparation equation; the proof now uses `prepareQueries_eq` to construct its handle rather than unfolding preparation again. |
| `Descriptor.changeOps` | Literal equality of the five stored arithmetic operations transports acceptance while retaining the complete raw descriptor and replay evidence. |
| `Descriptor.changeOps_raw` | The raw subject is literally preserved across operation equality. |
| `Descriptor.changeOps_evidence` | The entire replay is literally preserved; no checker or arithmetic producer is rerun. |
| `Descriptor.changeOps_self` | Identity transport preserves the complete descriptor using the public reassembly law. |
| `QueryHandle.changeOps` | Transports both the descriptor and canonical domain along all seven literal operation equalities, preserving the sign function and context. |
| `QueryHandle.changeOps_domain` | Identifies the retained domain with the actual operation-transported original domain. |
| `QueryHandle.changeOps_self` | Identity transport preserves the complete indexed handle by heterogeneous equality, composing descriptor/domain identity and checked reassembly. |

`QueryHandle.domain` and `QueryHandle.prepared` are individually documented.
The first stores computational preparation; the second binds every preparation
input and is erased at runtime. None of the three modules introduces a
semantic field/order instance. Runtime bodies and diagnostic behavior remain
unchanged. Mathematical construction success and root-sign correspondence
remain with the existing companion query-handle proofs.
