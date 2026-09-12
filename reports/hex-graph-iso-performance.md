# HexGraphIso performance

The executable benchmark suite is `hexgraphiso_bench`; its registrations
live in `bench/HexGraphIso/Bench.lean`. The comparator is
**nauty 2.9.3 (vendored source, in-process FFI through Hex.BenchOracle.Nauty)**.
Canonical upper-triangle agreement is required. Timing ratios are measured
observations; the per-node exponent check allows a margin of 0.2 against
nauty on families with enough sizes.

## Inputs and measured operations

| Input family | Coverage |
|---|---|
| `circulant-ladder` | Offset sets `{1,2}` and `{1,2,4,8}`; compiled operation and certificate benchmarks. |
| `random-gnp` | Fixed SplitMix64 seeds, Fisher–Yates relabellings and negative pairs. |
| `strongly-regular` | Paley, Latin-square, Johnson and Kneser graphs. |
| `grid-and-hypercube` | Sparse grids and hypercubes. |
| `decision-pairs` | Positive and negative pairs for executable decisions and kernel-checked tactics. |
| `native-sparse-path` | Native compressed construction from prepared path edges, from 1,024 to 65,536 vertices. |

The cactus driver measures public canonicalization, certificate-checked
canonicalization, nauty, and the corresponding decision tiers. Its `search`
mode measures raw canonical search with the `search_ns` column. Per-node
fits divide time by visited-node count so changes in traversal size remain
separate from work per node. The compiled suite also registers the declared
models for conversion, refinement, relabelling and validation.
The `runSparseBuild` benchmark times native sparse construction and consumes
both output arrays, with the input edge list prepared outside the timer.

## Measurements

The [canonicalization cactus](figures/hexgraphiso-canon-cactus.svg) and
[decision cactus](figures/hexgraphiso-pairs-cactus.svg) are generated from
source-fingerprinted records under `reports/bench-results/`. Their manifest
and freshness check bind them to the current implementation. Tactic timings
include the full proof route and retain timeouts.

The [six-way comparison](graphiso-comparison.md) adds the verified sparse
port to dense Hex, IsoGraph and the three C engines. The
[sparse validation report](sparse-nauty-validation.md) records native
construction scaling, adjacent performance comparisons, conformance and
imported kernel replay, with links to every retained measurement campaign.

Run `scripts/bench/graphiso_cactus_sweep.sh LABEL` on chungus2 to regenerate
the data, manifest and figures. Pin the command with `taskset -c "$(python3 scripts/bench/idle_core.py)"`
to select a CPU automatically. Retain completed observations and record host activity
as context. Before/after trials use adjacent arms and alternate AB/BA order.
`scripts/bench/graphiso_compare.py BASELINE CANDIDATE` reports timing ratios,
node-count changes and available provenance.

The [measurement archive](hex-graph-iso-evidence.md) retains compiled-suite,
search, allocation and replay observations with their original provenance.
Historical timings describe their recorded source revisions. The required
CI checks are result agreement, benchmark verification, sweep freshness,
and the per-node exponent margin.
