# Sparse nauty validation

The optimized sparse implementation has unconditional correctness and totality
proofs, including the total public API, complete automorphism generation, exact
orbits and group order, bounded certificate production, literal kernel replay,
public `graph_iso`, and Mathlib correspondence. The contracts and theorem names
are in the [computational SPEC](../HexGraphIso/SPEC/hex-graph-iso.md),
[Mathlib SPEC](../HexGraphIsoMathlib/SPEC/hex-graph-iso-mathlib.md), and
[proof plan](sparse-nauty-plan.md).

## Build, trust and conformance

The full `lake build` passes 13,719 jobs with Lean v4.34.0-rc2, including the
manual. The combined regression, conformance and proof-probe build passes
13,667 jobs, including dense, sparse and Mathlib probes and both CFI probes.
The published trust audit checks 1,924 Lean source files with no added axioms,
unfinished proofs or `native_decide`. Dependency and release-manifest checks
pass for all 57 split repositories and the aggregate. The benchmark import
audit passes for 50 executables and 216 build-only proof probes; all 24
`HexGraphIso.Bench` smoke checks pass.

The rebuilt executables pass the pinned nauty 2.9.3 campaign:

| Check | Cases |
|---|---:|
| Exact sparse indirect sorting | 130 |
| Exact sparse refinement | 220 |
| Sparse search, including exact integer group order | 45,491 |
| Sparse fixtures and automorphism groups | 6,233 |
| Dense fixtures | 6,233 |
| Dense generator/orbit/group fixture cases | 205 |
| Dense search traces | 39,032 |

Sparse labels, canonical adjacency, colours, all seven statistics, generators,
orbits and group orders agree with C. The complete sparse campaign, both fixture
streams and the dense trace stream are byte-for-byte unchanged from the preceding
validated implementation. Source and executable fingerprints accompany the
performance archives. The [integration validation record](bench-results/hexgraphiso-merge-validation.json)
retains the source commit, output digests, conformance results and proof-probe
diagnostics. CI selects both graph-isomorphism oracle streams under the
`HexGraphIso` library filter.

## Imported kernel replay

CI builds positive and negative random-pair and ordered-colour sparse proofs
through `HexGraphIsoSparseProofProbe`. The larger CFI negative proof is retained
under `conformance/HexGraphIso/Diagnostics` and builds manually through
`HexGraphIsoCfiDiagnostics`. These examples use ordinary `graph_iso` replay;
no paired timing report is required for this correctness surface.

## Preservation of native performance

The [adjacent comparison](bench-results/hexgraphiso-sparse-release-pairs.jsonl)
uses four alternating AB/BA blocks on eight fixed cases. Every result digest
agrees. Median new/previous canonicalization ratios range from 0.973 to 1.023:
the measurements show no substantial regression from integrating the proofs.
They do not establish an additional speedup.

The [integration comparison](bench-results/hexgraphiso-sparse-merge-pairs.jsonl)
repeats the same four AB/BA blocks after adopting the shared proof-module
layout and recovery API from `main`. All result digests agree, and median
ratios range from 0.994 to 1.014. The native sparse implementation is preserved;
the six-way campaign remains the measured comparison of its representation
choices.

Native path construction is registered with lean-bench as `runSparseBuild`.
The input edge list is prepared outside the timer; compressed construction and
consuming both output arrays are timed. Sizes range from 1,024 to 65,536,
with three trials per size. The
[first run](bench-results/hexgraphiso-sparse-build-release.json) retains all 21
successful measurements but is below the harness signal floor. A single
[longer-batch run](bench-results/hexgraphiso-sparse-build-release-batched.json)
uses the same sizes and implementation to resolve the scaling. Its medians
range from 98 microseconds to 6.26 milliseconds, consistent with linear
construction on this bounded-degree family. This is not a complexity claim
about arbitrary graph canonicalization.

The dense cactus refresh records source fingerprint `b6d628ac4165`. Its
freshness check and the required 0.2 per-node exponent check pass. Without the
removed replay limits, the tactic closes 33 of the 34 recorded pairs within
the unchanged 120-second timeout, compared with 31 in the preceding archive.
The remaining timeout is `neg-circ96-vs-2circ48`; it is recorded as unsolved.

The [final six-way comparison](graphiso-comparison.md) refreshes all four sparse
columns in two passes, retaining 2,486 process outcomes and 12,224 completed
timed calls. Four over-budget results and two process timeouts remain in the
archive. Hex sparse solves 310/333 cases; its median time ratios on shared
cases are 0.25 against Hex dense and 0.73 against IsoGraph. All 333 input hashes
match the preceding corpus; every retained historical cell is unchanged and
all solved sparse node counts match C exactly. The sparse per-node exponent
check passes its 0.2 tolerance on all 20 families.

The separate automorphism/certificate sweep retains 228 successful process
outcomes on 38 graphs. Every case succeeds in all three modes: complete
automorphism computation, certificate production and certificate replay.
All native measurement source hashes agree before and after the campaign.

All proof, integration and acceptance obligations in the sparse plan are
discharged. Publication through the monorepo release mechanism remains a
separate operation.
