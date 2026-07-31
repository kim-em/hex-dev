# Polynomial Factorization Performance

This report is the current cross-system performance snapshot for integer
polynomial factorization. It intentionally describes the current implementation
rather than preserving a history of earlier Hex routes.

## Measurement

- Hex revision: `081b7a679e2e0fb218068a14afed5b3102a3266e`
- Hex measurement: 2026-07-31
- External measurements: 2026-07-28; unchanged because this work changes only
  Hex
- Host: `chungus2`, AMD EPYC 9455, Linux x86-64
- Lean: `leanprover/lean4:v4.32.0-rc1`
- External systems: python-flint 0.9.0; PARI/GP 2.17.3 through cypari2
  2.2.4; NTL 11.6.0; Isabelle2025-2 with AFP 2026-05-29
- CPU placement: every timing command pinned with `taskset -c 0`
- Corpus: 392 rows, SHA-256
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`
- Protocol: persistent warm process, median of five when the first call is
  below one second, otherwise one call; ten-second per-call cutoff; no early
  termination

The fresh Hex record is
[`hexbz-factor-sweep-081b7a67-chungus2.json`](bench-results/hexbz-factor-sweep-081b7a67-chungus2.json).
Its SHA-256 is
`f4747b284a11b17b59b12faa1a93dd002387f671b53345f03b6034112dcbd9b6`.

## Current result

| System | Solved | Unsolved | Median | p90 | Slowest solved |
|---|---:|---:|---:|---:|---:|
| Hex factor | 375 | 17 | 338.141 µs | 6.995 ms | 8.130 s |
| FLINT | 391 | 1 | 66.850 µs | 1.184 ms | 1.228 s |
| PARI/GP | 391 | 1 | 99.958 µs | 1.254 ms | 823.201 ms |
| NTL | 391 | 1 | 135.631 µs | 2.714 ms | 1.919 s |
| Verified Isabelle BZ | 371 | 21 | 441.134 µs | 5.128 ms | 8.363 s |
| Verified Isabelle LLL | 314 | 78 | 6.109 ms | 1.219 s | 9.528 s |

Every pair of systems that answered a corpus row agreed on the factor-degree
multiset. Hex also answers `hoeij_M12_f132` in 1.653 s, where every retained
external comparator times out.

The important aggregate conclusion is mixed:

- Hex is ahead of verified Isabelle BZ on the matched corpus overall.
- FLINT, PARI/GP, and NTL remain substantially faster.
- Hex's long tail remains worse than its median: p90 is 6.995 ms despite the
  338.141 µs median.

## Paired comparisons

To suppress persistent-process noise, a pair is eligible only when both
measurements are at least ten times their own measured protocol overhead.
The Hex protocol floor is 19.599 µs.

| Pair, Hex / comparator | Eligible | Median ratio | p10–p90 | Hex faster | Comparator faster |
|---|---:|---:|---:|---:|---:|
| FLINT | 64 | 11.350× | 3.773×–92.284× | 0 | 64 |
| PARI/GP | 81 | 7.419× | 1.905×–79.688× | 0 | 81 |
| NTL | 170 | 4.236× | 0.957×–17.177× | 17 | 153 |
| Verified Isabelle BZ | 219 | 0.715× | 0.442×–2.516× | 140 | 79 |

A ratio below one favors Hex. The wide percentile bands mean none of these
comparisons is a uniform ordering over all polynomial families.

## Relative to Isabelle BZ by family

| Family | Eligible | Median Hex / Isabelle | Hex–Isabelle wins |
|---|---:|---:|---:|
| Chebyshev | 9 | 0.450× | 9–0 |
| Legendre | 13 | 0.560× | 12–1 |
| Random products | 26 | 0.553× | 26–0 |
| Conway | 91 | 0.682× | 52–39 |
| Laguerre | 13 | 0.732× | 13–0 |
| SD products | 7 | 0.774× | 4–3 |
| Cyclotomic products | 18 | 1.019× | 9–9 |
| Cyclotomic | 24 | 1.091× | 11–13 |
| Wilkinson | 12 | 1.328× | 1–11 |
| Swinnerton–Dyer | 6 | 2.796× | 3–3 |

The Chebyshev and Legendre goal is therefore achieved: they are now strong Hex
families rather than the principal deficit. The next useful optimization
frontier is Swinnerton–Dyer, wide cyclotomic products, and Wilkinson.

Representative timings make the boundary concrete:

| Row | Hex | Isabelle BZ |
|---|---:|---:|
| `chebyshev_T20` | 580.650 µs | 1.316 ms |
| `chebyshev_U24` | 662.522 µs | 1.472 ms |
| `legendre_P30` | 8.134 ms | 10.717 ms |
| `legendre_P38` | 4.568 ms | 6.743 ms |
| `sd5` | 108.855 ms | 22.827 ms |
| `sd5_shift1` | 96.471 ms | 14.875 ms |
| `sd4_x_sd4shift1` | 24.799 ms | 10.683 ms |
| `xpow120_minus1` | 514.891 ms | 169.354 ms |
| `cyclo_phi64_x_phi105` | 84.820 ms | 38.511 ms |

## What is being measured

There is one production direct-coordinate architecture:

1. normalize the polynomial once;
2. select and retain one direct modular prime plan;
3. Hensel-lift and run bounded head-forced classical recombination;
4. on a typed decline, pass that same modular plan to direct-coordinate CLD;
5. use exact trial division only as the total backstop.

There is no production monic-coordinate recombination fallback. The direct
classical iterator carries degree and trailing residue down the subset tree.
Before constructing a polynomial candidate, it proves and checks that the
raw trailing coefficient divides
`leadingCoeff(core) · target(0)`. The Mathlib proof relates the cached iterator
to the extensional support enumeration and proves that every genuine
irreducible support survives the filter.

The remaining SD5 cost is not accidental duplicate dispatch. Its selected
modular image has sixteen factors, and proving irreducibility still visits
32,768 head-forced supports. SD6-class inputs also show comparable
classical and CLD runtimes, so a width-only route switch does not solve the
long tail. Further work should separately measure:

- modular planning, Hensel lifting, filter survivors, candidate construction,
  exact division, and CLD lattice reduction;
- allocation and coefficient growth in the direct Hensel basis;
- CLD column count, lattice dimension, reduction iterations, and recovery
  precision.

Those counters are needed before and after any proposed SD/cyclotomic
optimization; total wall-clock alone cannot distinguish a better algorithm
from moving the same cost between tiers.

## Six decision-useful graphs

1. [Balanced combined cactus plot](figures/hexbz-cactus-combined.svg)
2. [Chebyshev runtime versus degree](figures/hexbz-runtime-degree-chebyshev.svg)
3. [Legendre runtime versus degree](figures/hexbz-runtime-degree-legendre.svg)
4. [Swinnerton–Dyer runtime versus degree](figures/hexbz-runtime-degree-swinnerton-dyer.svg)
5. [Cyclotomic-product runtime versus degree](figures/hexbz-runtime-degree-cyclotomic-products.svg)
6. [Hoeij–Zimmermann runtime versus degree](figures/hexbz-runtime-degree-hoeij-zimmermann.svg)

The default plot generation deliberately excludes superseded Hex diagnostic
routes. It shows the current public Hex implementation against FLINT, PARI/GP,
NTL, Isabelle BZ, and Isabelle LLL.
