# Sparse nauty implementation and validation

Count splitting uses one set of executable helpers for the initial scan,
three-way insertion, and fragment installation. The proofs share the
insertion contract through `splitCounts_induct`, then establish their own
boundary, activation, cache, or execution-trace property. This removes
repeated loop implementations and 564 lines of Lean overall. The
public sparse umbrella has nine imports instead of 110, preserving its
public import closure. The [source guide](../HexGraphIso/Nauty/Sparse/README.md)
describes the executable modules, proof contracts, indices, and array ownership.

The initial scan and insertion expand before compiler normalization;
the hash-state update is inlined. These compilation choices preserve the
nauty algorithm, including equal-key ordering, queue order, largest-fragment
ties, and both hash conventions.

## Correctness checks

| Check | Result |
| --- | --- |
| Full repository and manual build | 13,736 jobs passed |
| Release regressions, dense/sparse/Mathlib probes, and both CFI probes | 12,467 jobs passed |
| Published trust audit | 1,932 Lean files; no axioms, unfinished proofs, or `native_decide` |
| Exact sparse sorting | 130 comparisons passed |
| Exact sparse refinement | 220 comparisons passed |
| Sparse search and exact integer group order | 45,491 cases passed |
| Dense fixtures | 6,233 cases, including 205 automorphism-group cases |
| Sparse fixtures | 6,233 cases, all with automorphism-group checks |

The complete sparse search stream is byte-for-byte identical to the preserved
baseline. Both fixture streams match the committed fixtures. The imported
sparse kernel probes, including CFI, use only `propext`, `Classical.choice`,
and `Quot.sound`.

The [validation record](bench-results/hexgraphiso-sparse-cleanup-validation.json)
contains the output digests and probe diagnostics. The refreshed cactus and
pairs figures cover source fingerprint `3651af415613`; the 98-instance sweep,
34-pair sweep, tactic timings, and source manifest are retained under that
fingerprint in `reports/bench-results/`. Freshness and the required 0.2
per-node exponent check pass.

## Native performance

The baseline is commit `f566403719742868f2f9f16403c5609e8babe45a`, built in the
same worktree before editing. The [source and executable fingerprints](bench-results/hexgraphiso-sparse-cleanup-sources.json)
identify every measured variant. All measurements use the established eight
cases and fixed iteration counts. Each run selects one CPU automatically and
uses four adjacent blocks in alternating AB/BA order. Every completed sample
is retained.

The selected executable has [one comparison](bench-results/hexgraphiso-sparse-cleanup-macro-minima-pairs.jsonl)
and [one unchanged repeat](bench-results/hexgraphiso-sparse-cleanup-macro-minima-repeat-pairs.jsonl).
The final review adjustment compiles to byte-for-byte identical benchmark and
oracle executables, so these measurements apply to the reviewed source. The
table combines their eight ratios per case; values below one favor the selected
implementation.

| Case | Median selected/baseline time |
| --- | ---: |
| `gnp64-seed1` | 0.999 |
| `gnp128-seed1` | 1.003 |
| `gnp512-seed1` | 0.999 |
| `sparse1024` | 0.982 |
| `tree1024` | 0.969 |
| `cubic256` | 0.974 |
| `grid10x10` | 0.979 |
| `q7` | 0.981 |

These measurements show no consistent regression on the sampled workloads.
The three random cases remain within 0.4% of baseline; the other cases improve
by about 2–3%. Every result digest agrees. Absolute times and small differences
remain observations of the shared host.

The [ordinary-inlining comparison](bench-results/hexgraphiso-sparse-cleanup-pairs.jsonl),
its [unchanged repeat](bench-results/hexgraphiso-sparse-cleanup-repeat-pairs.jsonl),
and the [hash-only inlining comparison](bench-results/hexgraphiso-sparse-cleanup-inline-hash-pairs.jsonl)
are also retained. Those variants showed a consistent roughly 4% random-case
slowdown and are not the selected implementation.
