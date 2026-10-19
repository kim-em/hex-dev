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

Input constructors are part of this boundary. Canonical `One`/natural
constructors in closed input polynomials can reach native sign calculation
despite supplied replay operations; the kernel guard rejects those calls.
Explicit cached input constructors retain checked finite acceptance. A compiled
true result is not proof. The checked parent and its source identity remain
existing premises of this fixed-parent fixture, not automatically discovered
histories.

Missing literal scalar records, a same-degree changed head and a changed
endpoint yield exact evidence errors.
A zero quotation record-collection budget returns a structured missing-record
outcome without invoking scalar production; the full attempt collects the
three reached records. This uses the existing quotation collector, not a new
runtime arithmetic budget or operation-certificate framework. Original guard
preflight and exact context/domain/query bindings remain in the shared reader.

Default adapter/optional umbrella and existing conformance targets include the
core and nested fixture. The existing manual source chapter documents the
operation equality and fixed-parent example. No base rational import, owner
library, AGENTS.md, PLAN.md or CI job/workflow is changed.

`RootReplay.Result.coverage` and `ordered` now reuse the
[owner's supplied-replay laws](https://github.com/kim-em/hex-dev/pull/10903)
to establish exact interpreted-root coverage, value Nodup and strict ordering
for arbitrary accepted full derivative replay in a lawful real-closed model,
without a native producer equation. The
[complete supplied-cell checker](hexrcf-cell-replay.md) derives quantified
soundness from whole-line `.ok true` in a lawful ordinary-real parent model;
false remains diagnostic. The [fixed-algebraic matrix](hexrcf-algebraic-cells.md)
checks both sections and all three ordinary sectors for X²−√2 and quotes its
original real source. Arbitrary recursive source/provider/context history and
reached-data assembly, nonlinear sample conversion, all-live transport,
automatic common-field certification, accepted algebraic completeness, full
native/infinitesimal coverage and strict missing-predecessor compiled replay
remain part of #10358. This component does not register another handler or
close the issue. #10633/#10634's interfaces and measurement limits are preserved.

The [validation records](data/hexrcf-nested-root-replay/context.json) bind
selected source hashes, ordinary build/render outputs and the exact offline
proposal source/output. These are correctness and operational observations,
not performance or degree/precision/depth scaling evidence. `context.json` covers its recorded source commit; `review-context.json`
covers the revised source.

The [current validation](data/hexrcf-nested-root-replay/review-context.json)
also binds the quotation collector, strict coefficient reader and conformance
rule helpers. Seed and reached-record counts are asserted, the changed head
has the same degree, endpoint changes reject, and every rejection uses the
same per-descriptor producer guard as acceptance. Zero budget checks the
actual missing outcome and one recorded demand; its no-supplier-call property
follows from the existing collector's zero-fuel branch.
The [final validation](data/hexrcf-nested-root-replay/final-context.json)
also checks the supplier call flag directly and matches the limited attempt's
first polynomial request to the full attempt's first request. Visual captures
retain the separate source binding recorded in `review-context.json`.
