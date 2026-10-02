# Sparse output normalization without a minimum graph order

Canonical output uses membership-array counting whenever the graph order
`n` is at most eight times the row length `d`. The additional `n ≥ 128`
condition is removed. Short rows still use merge sort: always scanning all
vertices for every row would add quadratic work to sparse graphs. Both paths
have the same proved normalized result, and the replacement equality theorem
continues to compile. This changes output construction after the nauty search
has selected its label.

The change removes the dip between 96 and 128 vertices in the random-family
curve. The [current family plot](figures/hexgraphiso-comparison-families.png)
uses fresh canonicalization and output timings for all 102 corpus instances
below 128 vertices. Other measurement cells are retained from the
[preceding comparison](bench-results/hexgraphiso-comparison-optimized2-chungus2.jsonl).
The figure caption and metadata identify this scope. The search/conversion
figure retains its preceding measurements, since those stages do not call
the changed output routine.

## Adjacent measurements

Four fixed AB/BA blocks compare saved executables with and without the
minimum-order condition. Times below are medians of block means; speedups
are reciprocals of the median paired current/previous ratio. All results,
including regressions and control measurements, are retained in the
[raw pairs](bench-results/sparse-cutover/pairs.jsonl).

| Case | Previous canonicalization µs | Current µs | Paired speedup |
|---|---:|---:|---:|
| Random, 10 vertices | 7.619 | 7.392 | 1.03× |
| Random, 22 vertices | 25.915 | 20.514 | 1.26× |
| Random, 48 vertices | 103.137 | 60.486 | 1.70× |
| Random, 80 vertices | 289.072 | 138.167 | 2.10× |
| Random, 96 vertices | 427.858 | 191.347 | 2.24× |
| Random, 128 vertices | 327.614 | 332.495 | 0.99× |
| Cubic, 16 vertices | 101.972 | 102.802 | 0.99× |
| Cubic, 64 vertices | 1559.519 | 1536.483 | 1.02× |
| Tree, 16 vertices | 18.108 | 19.305 | 0.94× |
| Sparse random, 32 vertices | 32.436 | 28.892 | 1.12× |

The tree case is 6.6% slower, about 1.2 µs per call. The change therefore
does not improve every graph. The 128-vertex random control already used
counting, and the 64-vertex cubic control retains merge sort under the row
length guard; their small differences are retained without attributing a
new algorithmic effect. No replacement graph-order cutoff is introduced.

Output-only measurement on the 96-vertex random graph improves from
354.954 to 119.739 µs, a paired 2.97× speedup. On the 10-vertex random graph
it improves from 2.164 to 1.950 µs, or 1.11×. These stage timings are measured
independently of complete canonicalization.

The refreshed plot records 194.399 µs at 96 vertices and retains 332.082 µs
at 128 vertices. These are minima from the two-pass comparison protocol;
the adjacent experiment above supplies the separate before/after evidence.

## Validation and reproduction

`lake build hexgraphiso_sparse_bench hexgraphiso_sparse_probe
hexgraphiso_emit_sparse HexGraphIso.SparseTests HexGraphIsoMathlib` passes
all 2,238 jobs. The sparse C campaign passes 45,491 searches, 220 refinements,
and 130 indirect-sort comparisons. Its complete output hash matches the
preceding campaign. All 6,233 sparse fixtures remain byte-identical and pass
their C oracle. Sparse search correctness and totality proofs remain pending.
The dense cactus, pair, and tactic sweep is refreshed for source fingerprint
`d89b0d458615`; its freshness check passes. The published trust-surface check
also passes with no axioms, sorries, or `native_decide`.

Measurements use chungus2, AMD EPYC 9455, Lean 4.34.0-rc2. Each comparison
automatically selects and pins one CPU; shared-host load is retained as
context. There are no sample exclusions, unchanged reruns, or new profiles.
The source change, binary hashes, fixed paired schedule, affected input
hashes, and fixture checks are retained in
[the evidence directory](bench-results/sparse-cutover/).

The scoped sweep runs canonicalization and output for each affected input
in two passes, retaining all 408 successful process results and every timed
repetition. It preserves the five-second budget and family give-up rule.
The [merged data](bench-results/hexgraphiso-comparison-cutover-chungus2.jsonl)
is reconstructed from these records and the preceding comparison; untouched
cells retain their exact values. All 310 solved instances retain exact
agreement with C sparse's visited-node count. The
[metadata](bench-results/hexgraphiso-cutover-chungus2.meta.json) identifies
both sources of measurements and records the reconstruction checks.

To render the current plots:

```sh
uv run --no-project --with matplotlib==3.11.1 python scripts/plots/hexgraphiso-comparison.py \
  --data reports/bench-results/hexgraphiso-comparison-cutover-chungus2.jsonl \
  --machine 'chungus2 (AMD EPYC 9455)' --sparse-refresh-below 128
```
