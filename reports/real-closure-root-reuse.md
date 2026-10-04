# Cached selected-root search

An immutable inclusion cache retains each original predecessor and its checked
map. It also retains the mapped selected generators once per insertion, maps
them once on extension, and removes structurally duplicate images on insertion
and append. Searches do not recompute the original generators or their images.
Each candidate and its negative must satisfy the converted defining equation,
derivative signs, and strict finite bounds. Linear heads first provide their
coefficient-field root. This is a finite candidate search; arbitrary expressions
in several generators are not enumerated.

## Constraint order experiment

The [retained samples](bench-results/real-closure-root-reuse-order/results.json)
compare two orders of the same complete constraint list on the same actual
cached generators. Registered owners select the positive roots of `X^d-2`
and, with two owners, `X^d-3`. The unsuccessful query is `X²-11` on `(3,4)`
or `X⁴-17` on `(2,3)`. Every completed sample returns no cached match.
Setup and descriptor validation are outside the timed region. This experiment
isolates constraint order; it does not compare complete gathering implementations.

Two trials use adjacent head/bounds then bounds/head arms. Each sample performs
three searches on one automatically leased CPU. All 16 samples are retained,
including the host context and the exact compiled source. Values below are
means per search on this host.

| Degree | Distinct owners | Head first | Bounds first | Bounds/head |
| --- | --- | --- | --- | --- |
| 2 | 1 | 30.2 µs | 39.4 µs | 1.30 |
| 2 | 2 | 98.1 µs | 121.3 µs | 1.24 |
| 4 | 1 | 375.0 µs | 92.1 µs | 0.25 |
| 4 | 2 | 1332.0 µs | 292.4 µs | 0.22 |

Head first wins for these quadratic queries; bounds first wins for these
quartic queries. The default remains head first. A universal reordering is
not supported by these mixed results. Broader high-degree and nested workloads
remain part of the full tower Phase 4 evaluation. This focused experiment is
neither a complete Phase 4 result nor evidence for all cache-search workloads.

Reproduce a compiled sample with
`lake exe hexrealclosure_bench reuse-order 4 2 bounds 3`.
The [source capture](bench-results/real-closure-root-reuse-order/Bench.lean.txt)
and [measurement script](bench-results/real-closure-root-reuse-order/measure.py.txt)
retain the experiment exactly. The script's original host paths identify this
capture; adjust paths when running on another checkout.
