# Original-packing replay for a selected row

The selected-row regression uses the owner's `Algebraic.Packing` and eight
`Element.replay*` operations in the original positive-root field. Its source
statement remains `∃ x : ℝ, x² = Real.sqrt 2 ∧ 1 < x ∧ x < 2`.
The upper root and original real model are supplied by the existing checked
fixture. This inventory covers the row's predecessor arithmetic; source coefficients use authenticated `Element.restore`, while the
upper descriptor and row packet still use the existing scalar-fact path.

## Evidence and original identities

[The frozen inventory](../conformance-fixtures/HexRCF/selected-packing.json)
contains 42 distinct records captured from historical row collection and one additional
nonzero original polynomial `X² − 2` that retains zero at the selected root.
Its 43 original keys are distinct. Seven records change the representative;
original degrees are at most two and retained degrees at most one.
Each record supplies original and retained polynomials, the claimed scalar
sign and both scalar and joint graph packets. The joint queries bind the
retained representative and the zero difference from its original at the same
selected root. The owner reader checks reduction, signs, context and root.

[The replay module](../conformance/HexRCF/SelectedRoot/PackingReplay.lean)
persists `record0` through `record42` and a named `read` law for each literal
packet. Every law passes ordinary kernel checking with active native-producer
diagnostics. The accepted row uses zero producer fuel and has no unresolved
request. The fresh original-goal theorem, all packet laws and semantic bridges
have only `propext`, `Classical.choice` and `Quot.sound` as axioms. The additional
vanishing record has a nonzero original, zero representative, zero sign and
value equal to canonical zero.

[The refusal tests](../conformance/HexRCF/SelectedRoot/PackingMissing.lean)
remove the original −α² record while retaining the equal reduced −2 key,
and separately remove a literal zero and a nonzero constant. Their fixture
preconditions, exact missing original polynomial and context are kernel
checked. All three stop before a Boolean verdict. A fourth control swaps the joint
packet for −α² with the −2 packet; the literal reader rejects the different
original query despite the shared representative. Active diagnostic guards
check the actual replay transformations; trivial key/context identities are
ordinary kernel reflexivity checks, without artificial unfolding requirements.
The swapped packets' equal retained key, claimed sign and scalar graph, and
their different originals, are kernel checked. The audit also checks the
actual inventory body against all 43 named records in their exact order.
Records control replay progress and original identity. Operation agreement
makes accepted row semantics independent of which valid inventory is supplied.

[The audit](../conformance/HexRCF/SelectedRoot/PackingAudit.lean) checks the
complete 1,322-definition literal closure, including the packet count. Its
foreign allowlist contains only signed-integer/natural numeral machinery and
the JSON type alias, with constructors/projections/proofs handled separately.
All 43 actual packet-law bodies and the actual row-acceptance body are rechecked
under the native-producer diagnostic guard. The existing
[converter](../scripts/rcf/selected_literals.py) regenerates this module and all
five earlier selected-root modules in the existing CI check.

## Recorded build and structure

[Context and retained logs](data/hexrcf-selected-packing/build-context.json)
separate the earlier 42-request prototype, the first fresh frozen replay,
a failed changed-source audit, actual workspace integration and the final
canonical-zero/manual build, followed by the current-main affected build. The failed audit remains a failure; the corrected
integration passes. The workspace fixture build reports 130 seconds for replay,
19 for refusals and 35 for the complete audit. These are operational module
observations on the shared host, not a controlled speed comparison or scaling
campaign. A separate build validates the canonical-zero equality and manual.
The current-main build passes all 81 affected RCF, optional adapter and manual
targets (13,913 Lake jobs), including the original rational regressions.
It reports 125 seconds for replay, 18 for refusals and 37 for the audit;
these additional observations likewise establish no speed comparison. The
changed-source captures are unpaired shared-host builds; their different
elapsed times do not isolate an algorithmic or source-change effect.
A later changed-source build validates the swapped joint-packet refusal and
the strengthened zero precondition (13,851 jobs). It reports 245 seconds for
replay, 29 for refusals and 43 for the audit; the capture is retained separately.
The inventory-order and swapped-packet premises pass a further focused
10,857-job build. Its first declaration-syntax failure is retained separately
from the corrected successful capture.
The first current-main full manual render passes 13,828 jobs; the packing paragraphs are
inspected at desktop and narrow widths.

The compact JSON file is 230,192 bytes. Its 86 scalar/joint graphs store 171
nodes; recursively expanding their root references visits 172 occurrences.
These counts cover each packet independently, including stored nodes, and do
not assert a general DAG-sharing or performance gain. Constructor sharing is
separate from graph sharing. No aggregate memory measurement is claimed.

## Completion limits

This is one ordinary selected-root row with its supplied faithful parent model.
It adds no general context catalog, full carrier/root coverage, frontend total
acceptance, algebraic progress or recursive finite-joint realization. The
kernel's opaque missing-record boundary refuses incomplete replay; compiled
missing-record fallback and inverse arithmetic retain their owner behavior.
This is not a strict production-free checker for arbitrary compiled dictionaries.
The adapter's [full evidence inventory](hexrcf-adapter-evidence.md) and
[selected-row report](hexrcf-selected-root.md) retain those broader limits.
