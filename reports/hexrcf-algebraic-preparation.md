# Native algebraic source preparation

[`AlgebraicPreparation.prepare`](../adapters/HexRCF/RealCoefficients/AlgebraicPreparation.lean)
connects the shared source frontend to the original-input native packet API.
It preserves the reifier's coefficient order and original divisor inventory,
interprets both through `Coefficients.interpret`, and checks each resulting
source equality in the ordinary kernel. Preparation shares reflection
accounting with the source reifier rather than restarting the budget for each
coordinate. The default callback attempts routine radical-base nonnegativity; callers may
supply other ordinary proofs. Incorrect proofs are rejected.

The environment stores executable coefficient proposals first, followed by
every original divisor proposal. Separate finite indices retain the two roles,
including a divisor absent from the normalized coefficient tuple. `build` calls
the existing `AlgebraicCells.build`; it does not require an adapter primitive
common-field irreducibility certificate. This is a source preparation API, not
a new tactic handler. Its identities concern the retained algebraic expressions.
They do not establish that independently quoted literals denote the compiled
proposals, nor reconstruct frozen source/provider/predecessor histories.

The [conformance module](../conformance/HexRCF/AlgebraicPreparationConformance.lean)
checks independent square-root inputs, the actual source identity bodies and
their transitive axioms, ordered original guards, guard-only constants, both
true and false native verdicts, and retained half-open domain atoms. A budget
that fits source reification alone refuses additional coefficient work.
Incorrect nonnegativity proofs, unregistered constants and variable-dependent
denominators remain failures. Failure restores metavariables and a deliberately
created declaration; a cancelled zero divisor cannot enter root production.

Preparation scopes its proof auxiliaries under a fresh private prefix. The
conformance checks that property directly. The initial full manual import
exposed a collision between an unscoped `_proof_2` and another chapter; its
failed log is retained. The scoped implementation at
`91d504b1aac6a43b580e1e6d2a1b95fd38c2e439` passes the 11,768-job affected
selection, including the optional umbrella, conformance and changed manual
chapter (15.494 s, 2 GiB peak, zero swap). This is an operational build
observation, not a timing comparison. The later full render checks the combined
manual import as well as this chapter's code.

The scoped implementation's 14,297-job full render also passes. Its first
narrow capture exposed five pixels of local code overflow. The retained failed
capture identifies the guard-count line; the corrected example binds that
inventory before checking its size. The resulting source at
`694e85356ca2d19eaadb15ae87130dbc1791ca4b` passes the same 11,768-job affected
selection (12.867 s, 1.7 GiB peak, zero swap). This change concerns manual
layout; it does not change the preparation implementation.
The corrected full render passes 14,297 jobs (2m31.605s, 2.2 GiB peak,
zero swap). All six final desktop/narrow API and scope captures were opened;
the changed code and prose have zero local overflow. Start and end captures
show the same code block at distinct scroll offsets, with all its lines visible.

The checkpoint implementation at `6db3d5f7cd4f9cf9c52b6f11c0838d17b58fbb1c`
placed cancellation checks around coefficient/formula evaluation and native
production. Its pure `let` did not establish the optimized order of the
post-build check. The checkpoint record's check-placement description is not
proof of that runtime order; the strict barrier below supersedes that claim.
`Environment.buildWith` used a meta continuation because the complete packet
lives in a higher universe than a `MetaM` result. The retained `affected-6`
failure is the rejected attempt to return that packet directly in `MetaM`.
The subsequent full 14,296-job manual/optional/conformance integration passes
(3m39.505s, 6.4 GiB peak, zero swap), with the display unchanged from its
separate render. The [checkpoint record](data/hexrcf-algebraic-preparation/checkpoint-context.json)
retains that exact earlier implementation and validation scope.

The current API names the prepared record `AlgebraicPreparation.Inputs`.
`Inputs.buildWith` passes the native result as a strict argument to a helper
marked `noinline` and `nospecialize`. Optimized compiler output shows the
native build call before that helper; the helper checks cancellation before
calling the consumer. This avoids returning the higher-universe packet through
`BaseIO`/`MetaM` and preserves both checks without relying on pure-let placement.
The native call itself still has no internal checkpoint or arithmetic budget.
The conformance requires successful source-only reification under the tight
budget before checking aggregate exhaustion. It directly checks original
source divisor order, requires a retained semantically zero algebraic guard to
produce exactly `.divisor`, and builds both true and false nonempty irrational
coefficient inputs. The routine nonnegativity callback is public and used by
default; its negative-base decline and the structured unsupported result are
checked separately. Failure deliberately creates a fresh metavariable and a
declaration before rollback is tested. Tagged heartbeat, recursion-depth and
interruption boundary tests use a test-only observer over the shared state
references. A separate importing module requires the end-of-run marker, so an
escaped test interrupt cannot count as a completed run. Lean's standard catch
already preserves resource tags; the callback now uses a finalizer to restore
state on those exceptions as well as normal decline.

The [corrected-source record](data/hexrcf-algebraic-preparation/corrective-context.json)
binds the current implementation, compiler trace and completed regressions to
their source commit. Its 14,302-job optional/conformance/fresh-quotation/full-manual
selection passes in 4m14.374s at 4 GiB peak with zero swap. Both the cases' own
completion message and the separate importing module's check are present.
The retained `resources-3` attempt reported aggregate build success after an
escaped test interrupt, but lacks the completion message; it is explicitly
excluded as a completed regression. The final tests observe tagged exceptions
without restoring state on behalf of production code. The full manual render
passes 14,297 jobs (25.061s, 2.3 GiB peak, zero swap); its browser inspection
takes 10.401s at 2.9 GiB peak with zero swap. All six final desktop/narrow captures
were opened and have zero local overflow. These incremental build/render
observations are separate scopes, not performance comparisons.

The [current-main integration](data/hexrcf-algebraic-preparation/main-context.json)
at `e9b99f9f9fb8ffdd03f67a6b29979e13d5caad1c` consumes the actual merged
bounded-range replay optimization from #10941 and the subsequent owner/API and
library acceptance changes through upstream `370a081b44`. Its expanded
14,300-job selection passes, including fresh original guarded/unguarded and
Boolean quotation bodies, both native input suites, serialization/execution
audits, the optional umbrella and the full manual (13m19.132s, 13.2 GiB peak,
zero swap). Metadata checks cover 650 cones/1,550 modules, with both eleven-test
checker suites passing. No protected-instruction, SPEC, workflow or owner-source
changes remain in the adapter's diff against that upstream tree. This wider
rebuild is a distinct validation scope, not a before/after performance result.

## Quotation boundaries

Whole-coefficient presentations remain the native API's input convention.
Frozen quotation can instead retain atomic algebraic generators and derive
compound coordinate and divisor identities through the actual model's
arithmetic laws, while keeping the source schema's maximal closed coefficients.
Native preparation alone does not select or authenticate such a frozen layout.

A direct probe applying the public `NativeChain.ofContext` to a closed selected
presentation factory expression reaches the extraction call, then exhausts
2,400,000 heartbeats in `isDefEq` (57.109s, 12.3 GiB peak, zero swap). This
identifies a costly reduction path; it does not prove a mathematical API is
missing or that a different reconstruction is impossible.

The ordinary public-module reduction boundary has a smaller independent probe.
A fresh `module` importing only `HexRCF.RealCoefficients` cannot prove rejection
of an empty malformed rational `Codec.readGraph` input with `decide +kernel`:
reduction remains stuck at that reader. The otherwise identical control with
`import all HexSignDet.Codec` passes ordinary kernel checking. The private
import is retained solely as a diagnostic control, not introduced into the
adapter or proposed as the production boundary. A public reader equation or
exposure is needed for this direct reduction path. This probe does not claim
complete packet acceptance or audit every deeper reader dependency.

The retained `CellWith` prototype verifies supplied-operation specialization
and radical-check equalities against the canonical operations. Complete
operation-parametric root/cell parsing and final fold acceptance are separate
remaining implementation work. Existing owner record assembly can supply
checked arithmetic dictionaries; its compiled missing-record fallback is
still distinct from strict rejection of arbitrary omitted records.

## Retained native stress diagnosis

The previously interrupted automatic-input stress case is unchanged:
x² = √2 with 1 < x < √3, its selected negative-conjugate control, and every
original guard. Two instrumented build-only probes call the same public
presentation, gathering, specialization, partition, carrier/root and cell
APIs. Their explicit event files identify completed stages even while Lake
buffers command output. `original-input-stages-3-current.events` retains the
appended stream: its first seven lines belong to the earlier stage-2 run,
followed by the detailed stage-3 run. Those earlier lines are not extra stage-3
observations. These are Mathlib-facing diagnostic probes, not
Mathlib-free executable benchmarks or proofs of the original real goal.

Both probes were operator-interrupted and have no final accepted verdict.
Their sources retain the negative-conjugate control, but neither run reached it.
The first ran 2m37.652s; the more detailed second ran 5m10.943s. Both report
1 GiB peak and zero swap. The wrapper's `result: success` accompanies
`code=killed, status=15/TERM`; it is not a completed Lake build.

The detailed positive-input trace records original guard preflight, selected
presentations and gathering, three specialized atoms, and a native partition
with four distinct roots. Converted guard preflight and construction of the
degree-four product also complete. Radical reduction completes after 30.907 s
in that trace, retaining degree four. `RootBuild.build` then completes the
four-root table in 227.667 s, followed by 4.327 s for sector requests. The
last event starts cell-row production; no completed cell packet or replay
verdict is recorded before interruption. Thus the retained trace separates
complete root-table construction from the earlier partition and radical stages
and the subsequent row work. It does not identify a particular inner query,
establish a scaling law or prove a speedup.

These diagnostics narrow the unresolved cost in the complete native path;
they do not replace the stronger stress acceptance or the full #10358
performance obligations. Earlier interrupted samples and source-bound reports
remain preserved. The [record](data/hexrcf-algebraic-preparation/context.json)
binds its pinned `694e85356ca2d19eaadb15ae87130dbc1791ca4b` implementation,
probe sources, raw failed and successful
logs, event files and validation artifacts. All own Lean/Lake/rendering work
remains serial under aggregate 32 GiB/no swap/two Lean threads.

The general extension still needs authenticated quoted proposals and frozen
history/reached-data assembly, strict rejection of arbitrary missing records
in compiled replay, general source quotation and accepted completeness, and
the remaining transport, realization and performance evidence. Native source
identities and packet production do not discharge those obligations.
