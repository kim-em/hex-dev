# Fixed-field input costs and proof attribution

The implementation question is whether increasing source degree, source comparison atoms
or integer coefficient width independently increases end-to-end module build
time on a fixed selected field. Six fresh proof modules use matching optional
adapter imports and the same positive square root of 2. Each pair changes one
input dimension. Every carrier has no real roots; these comparisons measure
that regime, not root separation, growing number-field degree or tower depth.
All actual quoted theorems have only `propext`, `Classical.choice` and `Quot.sound`.

The [raw results](bench-results/hex-rcf-scaling-proofs-8f7f337caffe-chungus2.json)
and [arm records](bench-results/hex-rcf-scaling-proofs-8f7f337caffe-chungus2.json.samples.jsonl)
retain all 24 completed builds from clean source
`8f7f337caffe74f11a285bc69aae294b818d6ab3`, Lean 4.35.0-rc3, shared host
`chungus2`, automatically leased CPU 86, sibling 38 and one Lean thread. Four
trial-major rounds rotate the three pairs; adjacent arms alternate AB/BA.
Lake startup, dependency replay, abstraction, quotation and checking are included.
No host observation removes a sample; there was no rerun.
The original v1 records used `reference`/`candidate` metadata keys that the
harness replaced with module records; the dimension values are recoverable
from the retained module identities and source hashes. The current runner
uses `reference_value`/`candidate_value` and schema v2. The original v1 data
is retained unchanged.

| Changed input | Reference / candidate | Median build seconds | Median paired difference seconds | Median peak RSS KiB |
| --- | --- | --- | ---: | --- |
| Variable degree | 2 / 4 | 8.514 / 8.558 | 0.007 | 3,479,900 / 3,486,484 |
| Source comparison atoms | 1 / 4 | 8.519 / 8.937 | 0.412 | 3,484,632 / 3,496,516 |
| Integer coefficient bits | 32 / 128 | 8.602 / 8.482 | 0.021 | 3,485,872 / 3,485,502 |

The four paired differences are respectively `[-0.316, 0.117, -0.052, 0.066]`,
`[0.468, -0.018, 0.544, 0.357]` and `[-0.069, 0.290, -0.171, 0.111]` seconds.
The atom pair adds three syntactically different constant positivity
comparisons, preserving carrier degree and maximum coefficient width. Its
one/four counts refer to source comparisons, not normalized sign-table keys
or independent sign questions. Its three positive margins are observations,
not a resolved complexity law. The harness reports `no-comparable-control` for
all pairs. There is no speedup claim from the coefficient-width medians.
Host context includes up to 19 concurrent Lean/Lake processes; maximum sibling
busy ratio was 0.026 and measurement-CPU foreign ratio 0.002. These observations
are context, not validity thresholds.

These two-point, end-to-end comparisons are neither parametric complexity
registrations nor fixed-budget attestations. They have no independently derived
tight wall-time model, upper-bound verdict or operation-specific ceiling. Full
Phase-4 cost attestation remains blocked under the benchmarking mode order;
a generic timeout does not supply a scientific budget. Precision and nested
depth, bounded failures and common/repeated-root scaling remain separate work.
The earlier [root-section report](hexrcf-production-proofs.md) preserves actual
close-section/further-root observations without claiming independent scaling.

## Shared syntax and serialized evidence

The [structural audit](data/hexrcf-scaling-sharing/998654440/audit.json) and
[compiler output](data/hexrcf-scaling-sharing/998654440/compiler.log) inspect the
same six proof bodies at clean source `99865444095dd7c057cb2ef9ca73b78a4fc4d337`.
That revision adds a reusable counter and an exact local-reference fixture;
the probe bodies are unchanged from the timing revision. Artifact hashes and
source closure hashes are recorded separately. Inspection imports private
bodies; the proof modules themselves use ordinary imports.

| Proof module | Unique syntax nodes | Local expression trees | Expanded local references | Public / private olean bytes |
| --- | ---: | ---: | ---: | --- |
| Degree2 | 13,000 | 24,115,571,256 | 24,115,575,390 | 70,712 / 476,776 |
| Degree4 | 13,057 | 27,044,257,594 | 27,044,261,728 | 70,752 / 478,576 |
| Atoms1 | 13,139 | 24,383,758,408 | 24,383,762,542 | 72,128 / 480,408 |
| Atoms4 | 13,640 | 28,790,074,266 | 28,790,078,400 | 72,680 / 510,720 |
| Bits32 | 13,143 | 24,383,758,352 | 24,383,762,486 | 71,928 / 480,408 |
| Bits128 | 13,147 | 24,383,758,352 | 24,383,762,486 | 72,048 / 528,328 |

Each proof reaches seven declarations in its own module. Structurally equal
Lean expressions count once under `Expr.eqv`; binder names and annotations do
not distinguish nodes. Literal nodes count once irrespective of bit width,
which explains why coefficient-width changes primarily appear in serialized
bytes. Local tree counts include each reachable declaration type/body once,
with constants as leaves. Expanded counts substitute local type/body at every
reference. Imported declaration bodies, universe-level nodes and binder-name
nodes are excluded. Huge tree counts show representational sharing; they do
not count physical heap objects, executed operations or kernel runtime.

The counter checks small trees, depth-40 repeated syntax and a two-node
`Bool.true` declaration from a separate fixture module. For the local constant
reference the exact counts are surface 1, expanded 3, unique 3 and one local
declaration. This directly checks the local-reference rule independently of
the large quoted proofs.

## Representative phase attribution

The [single retained profile](data/hexrcf-phase-profile/da312db57/audit.json),
[compiler log](data/hexrcf-phase-profile/da312db57/compiler.log) and
[dependency warm log](data/hexrcf-phase-profile/da312db57/warm.log) come from clean
source `da312db57a8b443ec156beb2176740f72d6addb5`, leased CPU 14 and one Lean
thread. The ordinary-import theorem is
`∃ x : ℝ, x² = √2 ∧ 1 < x ∧ x < √3`. It joins two independently constructed
fields, computes a further root, and checks ordinary real root/sector samples.
This revision used full Sturm-query quotation, before interval-sign quotation
was introduced. These category times do not describe the current default.
Its standard-axiom audit passes. It has no symbolic infinitesimal realization
phase; no absent `Sample.realizeReplay` computation is charged as zero.

The fresh build took 43.672 seconds and peaked at 6,183,004 KiB RSS. Public and
private olean sizes were 71,416 and 1,444,032 bytes. Lean's profiler records
**exclusive** category times; child categories are subtracted from parents.

| Category | Exclusive time |
| --- | ---: |
| Source preparation | 129 ms |
| Source authentication | 6.22 ms |
| Common-field construction | 19.2 ms |
| Algebraic frontend | 283 ms |
| Certificate production | 167 ms |
| Literal quotation | 249 ms |
| Literal replay | 24.3 ms |
| Type checking, across all calls | 30.1 s |
| Handler candidate check | 29.9 ms |
| Elaboration | 7.1 ms |

The literal replay figure excludes its child kernel checks, including calls
reported at 13.2, 12.1 and 4.24 seconds. It is not the total replay cost.
Type checking dominates this representative proof; the 43.672-second build
also includes Lake/dependency replay, compilation and profiler logging. The
profile does not establish the bottleneck of the six simpler timing probes or
an asymptotic bound. Reusing quoted evidence and reducing repeated kernel
checking are concrete performance questions for subsequent changes.

Native production/common-field calls use pure `profileit` thunks, confirmed in
generated C to enclose their operations. Meta phases use `profileitM`. Profiling is disabled by default in the adapters. A separate unpinned
[diagnostic log](data/hexrcf-phase-profile/initial-diagnostic/compiler.log),
[source patch](data/hexrcf-phase-profile/initial-diagnostic/source.patch),
[probe](data/hexrcf-phase-profile/initial-diagnostic/Profiling.lean) and
[scope](data/hexrcf-phase-profile/initial-diagnostic/scope.json) are retained
with native work outside their measured categories; those category values
are excluded from the representative attribution and are not pooled with it.

Reproduce the paired builds with `python3 scripts/bench/hexrcf_scaling_proofs.py`
from a clean checkout. Inspect syntax using
`python3 scripts/bench/hexrcf_production_sharing.py --suite scaling --output <new-directory>`.
Collect one representative profile with
`python3 scripts/bench/hexrcf_phase_profile.py --output <new-external-directory>`.
The profiler warms only dependencies, retains the completed sample before
validation, records source/dependency/host identities and never retries for
host activity. These are build-only modules, with no Mathlib-importing runtime
benchmark or new CI job. The profiling module belongs to the on-demand
`HexRCFProofProfile` target, so routine CI does not execute a scientific
attribution run. The six scaling proofs and counter fixtures remain in the
existing CI proof-probe target. The recorded profiling revision predates that
target separation and the rational-constructor lowering; its timings are tied
to the recorded source, not to subsequent revisions.
