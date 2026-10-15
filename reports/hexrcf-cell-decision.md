# Accepted typed cells in an ordinary real model

The optional RCF adapter proves existence of accepted complete typed cell
evidence and exact diagnostic semantics for the shared one-quantifier formula.
Its explicit domain is an actual lawful ordinary-real parent model with a
nonzero caller-supplied original divisor list. The proof constructs the
carrier, complete root table, sector points, selected-sign rows and point
bindings through the existing owner APIs. Caller-supplied root lists, ordinary
point functions and successful child-sign premises are unnecessary.

## Requested sectors and checked boundaries

[SectorRequest](../adapters/HexRCF/RealCoefficients/SectorRequest.lean) uses the
owner’s proved `Partition.sectorBetween?` API. A dependent conversion retains
the returned sample’s value in the actual common context and the same compatible
collection model. `Cut.adjacent` derives the requested endpoints for each cut
from the public whole-line, left-ray, right-ray and bounded-sector membership
laws, using list identities. `Cut.witness` supplies a point with proved
membership at those exact endpoints. `points` collects those executable
requests as a fixed-size vector; `points_spec` proves that every request
succeeds and every returned coordinate has the required membership. Both the
public `CellDiscover.run` and `sector_points` use this route. No new owner index
theorem is needed.

[CellAlignment](../adapters/HexRCF/RealCoefficients/CellAlignment.lean) relates
each boundary coordinate to the independently checked radical root list.
`sector_points` transports all requested memberships to the actual indexed
root cells. Its ordered-list equality is supplied by `aligned`, which derives
that equality from source conversion, carrier identities and the owner’s
complete coverage/order laws. The headline construction does not assume the
two root lists agree.

## Complete typed evidence

[CellProgress](../adapters/HexRCF/RealCoefficients/CellProgress.lean) obtains
selected rows through the actual `Descriptor.buildSigns_success` theorem.
The ordinary-point head interprets as `X - C point`; its domain, degree,
unique-root count and successful actual descriptor construction are proved.
The retained raw head and joint signs then construct a `PointRows.Packet`
at that exact ordinary point. `sector` constructs adjacent selected-sign
evidence with the required strict signs. `evidence` assembles every section,
ordinary sector and entire same-point source row.

[CellDecision](../adapters/HexRCF/RealCoefficients/CellDecision.lean) proves
strict-fold totality and exact semantics of the existing typed checker.
`complete` composes actual collection model existence, source-coordinate and
divisor conversion, radical/root preparation, ordered boundary agreement,
requested points and complete typed evidence. One constructed matrix supplies
both quantifiers. Each returned verdict is true exactly when the original
shared sentence holds at the original fixed coefficient values. False results
remain diagnostic for the tactic. Source reification must separately bind those
coordinates and supplied divisor expressions to a Lean goal.

The [fresh proof audit](../conformance/HexRCF/CellDecisionProofs.lean) rechecks
all 28 actual construction, reuse and decision proof bodies. It requires the real owner constructor, collection,
root/point and sign-law dependencies. The only permitted axioms are `propext`,
`Classical.choice` and `Quot.sound`. Existing supplied-cell quotation regressions
remain separate evidence for actual source-goal proof emission.

## Native construction and the observed cost

The [native regression](../conformance/HexRCF/CellRequestedConformance.lean)
uses generic finite cut indices and the actual boundary-request API to select
all points through the public `CellDiscover.run`. Regular conformance produces
and reads complete packets for six small matrices; the explicit
`lake build HexRCFCellRequestedStress` target retains the four-boundary union.
Together these seven matrices cover
an algebraic equation, true/false zero atoms, a repeated equation, its union
with literal half-open guards, and both endpoint controls. The complete
four-boundary union has roots `-sqrt(sqrt 2)`, `1`, `sqrt(sqrt 2)` and `2`.
No explicit list of sector points is supplied.

A retained scratch version of these seven cases passed in 329 seconds with
an observed 1.5G memory peak and zero swap. A separate diagnostic four-boundary
trace records 81 ms partition construction, 533 ms requested-point selection,
11,923 ms radical/root preparation, 258,044 ms complete cell-row production and
24,284 ms literal reading plus both folds. The whole diagnostic build took
317 seconds with an observed 7G peak and zero swap. These are build-only
observations on a shared host with Mathlib imports, not Mathlib-free runtime
benchmarks, scaling evidence or a speedup comparison. They identify row
production as the substantial unresolved cost in this input. The retained raw
profiles have limited caller attribution and do not identify a specific child
producer. Every completed sample, including the first profile’s map timeout,
is retained.

The [child-timed diagnostic](data/hexrcf-cell-decision/row-cost.json) runs the
actual existing child functions and validates the resulting complete matrix.
Its 22 calls record 71,140 ms for four section rows, 180,479 ms for eight
adjacent-root selected-sign queries, 368 ms for five ordinary-point descriptors
and 5,722 ms for their rows. These figures identify selected-sign production at
the carrier roots as the substantial cost in that trace. They do not establish
a general speedup or scaling result. The [existing owner API question](https://github.com/kim-em/hex-dev/issues/10377#issuecomment-6185385739)
asks whether prepared joint tables can be reused across descriptors with exact
context/head/domain/query bindings. No reusable search or replay implementation
is duplicated in the adapter.

## Remaining obligations

The headline theorem establishes mathematical existence of accepted typed
evidence. An operational theorem for the general executable builder and
serialization/reader acceptance remain separate. The native common-context
collection does not authenticate a frozen context/provider history. The
compiled fallback for arbitrary missing predecessor records remains outside
strict replay. No new tactic handler or coefficient representation is installed.

The ordinary parent model is an explicit hypothesis. This result does not
supply faithful formal models for arbitrary named constants; finite registered
successes retain their separate authenticated partial-reader obligations.
General source/provider/reached-data assembly, all-live transport, automatic
common-field certification, complete frontend execution/quotation and the
remaining native/infinitesimal obligations keep #10358 open. The substantial
native row cost also needs further investigation before any performance claim.

## Validation

The [source-bound record](data/hexrcf-cell-decision/context.json) binds the ten
implementation/manual/target files at `5a37b7f022`, retaining the full-build
source at `ebb48a914d` separately. The complete optional
adapter, conformance and manual build passes 14,689 jobs. It rechecks all 21
actual theorem bodies and required owner dependencies, and the public seven-case
native regression passes in 327 seconds. All seven structural checks pass,
including628 admission cones covering1,528 local modules and eleven scanner
regressions. Original rational and algebraic tactic examples remain in that
same full build.

The first full attempt at `b64a2b22df` passed the code and conformance targets
but rejected an ambiguous signature name in the manual example. A manual-only
change qualifies `Tower.Signature`; the subsequent full build passes. Both
attempts are retained. Their observed peaks were 14.5G and 3G respectively,
with zero swap; the second run reused completed build artifacts, so these
observations are not a before/after memory comparison. Every own build runs
serially in one aggregate 32GiB cgroup with zero swap and two Lean threads.

The [diagnostic record](data/hexrcf-cell-decision/diagnostics.json) separately
retains the earlier prototype source, seven-case result, per-stage timestamps,
both raw profile captures and their complete warnings/reports. It binds those
observations to their earlier adapter source rather than attributing them to
the final public port. The source record also retains the earlier port failure
and successful pre-cleanup audit separately from final-source validation.

The final manual-only layout revision at `5a37b7f022` splits long bindings and
uses the shared `QF` name through a namespace open. Its full manual build passes
14,260 jobs and the complete renderer passes 14,262. The earlier 45-pixel narrow
code overflow, its four partial captures and the failed browser record are
retained separately from the final desktop/narrow checks. The implementation
and conformance sources are unchanged by either manual correction.

All six final desktop/narrow captures were opened and inspected. The
[narrow API example](data/hexrcf-cell-decision/cell-decision-narrow-source.png),
explicit model domain and remaining-obligations prose fit their targets,
with zero descendant overflow. The browser check covers the changed content,
not unrelated horizontal overflow elsewhere in the complete manual.
