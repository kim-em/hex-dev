# Nested full-table replay with checked predecessor operations

[`RootTable`](../adapters/HexRCF/RealCoefficients/RootTable.lean) factors the
existing full-query graph replay and shared descriptor extraction over the
actual coefficient operation dictionaries. It retains the accepted tree,
literal root list and exact owner extraction equation. Equal-operation
transport uses the owner's `Descriptor.changeOps`, preserving literal subjects
and evidence while changing only proof indices. No coverage, mathematical
ordering or arithmetic law is invented in this adapter.

[`RootReplay.readWith`](../adapters/HexRCF/RealCoefficients/RootReplay.lean)
accepts five supplied operations and ordinary equality proofs. Replay and
derivative extraction use those operations; the result returns with canonical
indices. `readWith_eq` preserves the canonical reader's exact result, including
every error. Canonical `read` shares the same core, rather than maintaining a
second checker. The existing public Result fields and semantic statements
remain intact, and the earlier canonical conformance still passes.

The [frozen nested graph](../conformance-fixtures/HexRCF/nested-root-table.json)
was produced for X²−√2 in (1,2), over the existing checked positive √2 parent.
The [constructor renderer](../scripts/rcf/selected_literals.py) performs no
certificate production. The
[production conformance](../conformance/HexRCF/NestedRootProduceConformance.lean)
starts without old row facts: five independently checked scalar seeds come
from untrusted stored-coefficient hints, and three new records are supplied as
ordinary kernel replay demands them. Supplied keys are reduced and deduplicated,
then matched exactly to each request. Scalar packet acceptance is independently
checked before restoration and sharing.

The acceptance and one-root output-cardinality declarations activate ordinary
kernel diagnostics and forbid native root/scalar production and per-descriptor
replay. The result retains the checked domain and actual selected-root
interpretation at the same authenticated parent. A new source proof derives
`∃ x : ℝ, x²=√2 ∧ 1<x ∧ x<2` from that result, coefficient interpretation and
checked endpoints, without the older row-truth theorem. The
[fresh import module](../conformance/HexRCF/NestedRootOrdinaryConformance.lean)
checks the exact target and complete standard three-axiom inventory. Local
body scans consume the root/domain laws and reject producer constants;
imported declarations are leaves, not rechecked imported bodies.

Input constructors are part of this boundary. Initial prototypes left
canonical `One`/natural constructions in closed input polynomials, reaching
native sign calculation despite supplied replay operations. The kernel guard
rejected them. Explicit cached input constructors remove those calls. This
does not authorize weakening the guard or treating a compiled true result as
proof. The checked parent and its source identity remain existing premises of
this fixed-parent experiment, not automatically discovered histories.

Missing literal scalar records and a changed head yield exact evidence errors.
A zero quotation record-collection budget returns a structured missing-record
outcome without invoking scalar production; the full attempt collects the
three reached records. This uses the existing quotation collector, not a new
runtime arithmetic budget or operation-certificate framework. Original guard
preflight and exact context/domain/query bindings remain in the shared reader.

Default adapter/optional umbrella and existing conformance targets include the
core and nested fixture. The existing manual source chapter documents the
operation equality and fixed-parent example. No base rational import, owner
library, AGENTS.md, PLAN.md or CI job/workflow is changed.

Complete interpreted-root coverage, value Nodup and mathematical ordering for
supplied replay remain with the SignDet owner under the existing
[coverage request](https://github.com/kim-em/hex-dev/issues/10331#issuecomment-6126809036)
and [ordering request](https://github.com/kim-em/hex-dev/issues/10331#issuecomment-6129572591).
Arbitrary recursive provider/context history, nonlinear sample conversion,
complete cell replay, all-live transport, automatic common-field certification
and accepted algebraic completeness remain part of #10358. This component does
not register another handler or close the issue. #10633/#10634's interfaces and
measurement limits are preserved.

The [validation records](data/hexrcf-nested-root-replay/context.json) bind
selected source hashes, ordinary build/render outputs and the exact offline
proposal source/output. These are correctness and operational observations,
not performance or degree/precision/depth scaling evidence. Earlier prototype
failures are separate from successful integrated validation.
