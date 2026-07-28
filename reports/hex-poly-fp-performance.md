# HexPolyFp Performance Report

Current at revision `5c371a5abb85ca6ef6510ec60888f3048db71719`,
measured 2026-07-28 on `chungus2` (AMD EPYC 9455, Linux x86-64),
pinned to CPU 0.

The export records `5c371a5-dirty` because the benchmark registrations and
reports were being repaired in the same worktree; the measured library revision
is the full hash above.

## Bench Targets

The suite covers Frobenius remainder computation, GCD, weighted product,
square-free decomposition, powering, division, and modular composition.

## Verdicts

Three independent outer trials were run for every rung.

| Target | Model | Largest rung | Median | Verdict |
|---|---|---:|---:|---|
| Frobenius `X` mod | `n³` | 80 | 295.793 ms | inconclusive |
| GCD | `n²` | 256 | 44.938 µs | inconclusive; observed faster |
| Weighted product | `n²` | 4096 | 664.360 ms | consistent |
| Square-free decomposition | `n²` | 768 | 6.638 ms | consistent |
| Frobenius power mod | `n³` | 64 | 338.979 ms | consistent |
| Power mod monic | `n² log n` | 512 | 149.547 ms | consistent |
| Division mod | `n²` | 256 | 975.082 µs | consistent |
| Modular composition | `n³` | 192 | 368.882 ms | consistent |

Raw export:
`reports/bench-results/hex-poly-fp-5c371a5a-chungus2.json`
(SHA-256
`c705489ef726ee83acbd32b4f290d3bcb0251cf4181d8f4075f2bb1df218ce9b`).
`list` and `verify` passed.

## Comparator Ratios

No external comparator is declared for this headline suite. FLINT comparisons
for higher factorization layers are recorded in the HexBerlekamp and
HexHensel reports.

## Profile

No fresh sampling-profiler trace was collected in this refresh. The compiled
timing ladders cover the three prior profile groups directly:
`quotient-powers`, `modular-composition`, and `product-squarefree`.

## Concerns

- The `n²` GCD declaration is intentionally conservative; the current ladder
  scales close to linearly (`β=-1.034` after normalization).
- The direct Frobenius-`X` cubic verdict is inconclusive (`β=-0.249`).
- Modular composition remains the largest finite-field substrate cost in the
  representative degree-192 case.
