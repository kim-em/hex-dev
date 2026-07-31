# Polynomial Factorization Performance

This is the current cross-system performance snapshot for the supported
integer polynomial factorization function. It compares the one public Hex
implementation with optimized external libraries and two verified Isabelle
implementations.

## Measurement

- Hex source revision:
  `75291ae2fe6c58d95ba73dff9e5d2720df11b3d5`, with a clean worktree
- Hex executable SHA-256:
  `f1b2c4262493cc35c68b2c433bba3803d31f6a27631000f52a6ee295721a6fe4`
- Hex toolchain: `leanprover/lean4:v4.32.2`
- Measurement date: 2026-07-31
- External measurements: 2026-07-28, retained because their inputs did not
  change
- Host: `chungus2`, AMD EPYC 9455, Linux x86-64
- External systems: python-flint 0.9.0; PARI/GP 2.17.3 through cypari2
  2.2.4; NTL 11.6.0; Isabelle2025-2 with AFP 2026-05-29
- CPU placement: harness and service pinned to CPU 0
- Corpus: 392 rows, SHA-256
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`
- Protocol: persistent warm process, median of five when the first call is
  below one second, otherwise one call; ten-second per-call cutoff; no early
  termination

The durable Hex record is
[`hexbz-factor-sweep-75291ae2-chungus2.json`](bench-results/hexbz-factor-sweep-75291ae2-chungus2.json).
Its SHA-256 is
`5d8b08225a4f2a0c8288d9f536303193a2f54b312a1cbae57ffcac23cd6295bd`.
The record includes the full source revision, clean-worktree marker,
toolchain, corpus hash, host, repetition rule, cutoff, and measured protocol
overhead.

## Current result

| System | Answered | Timed out | Median | p90 | Slowest answer |
|---|---:|---:|---:|---:|---:|
| Hex factorization | 375 | 17 | 352.262 µs | 7.107 ms | 8.727 s |
| FLINT | 391 | 1 | 66.850 µs | 1.184 ms | 1.228 s |
| PARI/GP | 391 | 1 | 99.958 µs | 1.254 ms | 823.201 ms |
| NTL | 391 | 1 | 135.631 µs | 2.714 ms | 1.919 s |
| Verified Isabelle BZ | 371 | 21 | 441.134 µs | 5.128 ms | 8.363 s |
| Verified Isabelle LLL | 314 | 78 | 6.109 ms | 1.219 s | 9.528 s |

Every pair of systems that answered agreed on the multiset of factor degrees.
Hex also answers `hoeij_M12_f132` in 1.652 seconds, while all retained
external comparators time out.

The result is mixed:

- Hex is faster than verified Isabelle BZ on the matched corpus overall.
- FLINT, PARI/GP, and NTL remain substantially faster.
- Hex has a pronounced long tail despite its sub-millisecond median.

## Paired comparisons

A pair is eligible only when both measurements exceed ten times their own
service's measured protocol overhead. The Hex protocol floor is 20.120
microseconds.

| Hex / comparator | Eligible pairs | Median ratio | p10 to p90 | Hex wins | Comparator wins |
|---|---:|---:|---:|---:|---:|
| FLINT | 64 | 11.680× | 3.893× to 91.139× | 0 | 64 |
| PARI/GP | 81 | 7.650× | 1.932× to 81.228× | 0 | 81 |
| NTL | 170 | 4.360× | 1.045× to 17.732× | 17 | 153 |
| Verified Isabelle BZ | 218 | 0.734× | 0.460× to 2.552× | 137 | 81 |

A ratio below one favors Hex. The broad percentile bands show that no row of
this table is a uniform ordering across polynomial families.

## Relative to verified Isabelle BZ by family

| Family | Eligible pairs | Median Hex / Isabelle | Hex wins |
|---|---:|---:|---:|
| Chebyshev | 9 | 0.469× | 9 |
| Conway | 90 | 0.693× | 50 |
| Cyclotomic | 24 | 1.112× | 10 |
| Cyclotomic products | 18 | 1.046× | 9 |
| Laguerre | 13 | 0.757× | 13 |
| Legendre | 13 | 0.576× | 12 |
| Random products | 26 | 0.555× | 26 |
| Swinnerton-Dyer products | 7 | 0.798× | 4 |
| Swinnerton-Dyer | 6 | 2.772× | 3 |
| Wilkinson | 12 | 1.369× | 1 |

Hoeij-Zimmermann has no common answered row with verified Isabelle BZ.
Chebyshev and Legendre are now strong Hex families. The most useful next
optimization targets are plain Swinnerton-Dyer, Wilkinson, parts of the
cyclotomic families, and the Hoeij-Zimmermann coverage gap.

Representative timings show the family differences:

| Row | Hex | Isabelle BZ |
|---|---:|---:|
| `chebyshev_T20` | 616.595 µs | 1.316 ms |
| `chebyshev_U24` | 674.682 µs | 1.472 ms |
| `legendre_P30` | 8.391 ms | 10.717 ms |
| `legendre_P38` | 4.755 ms | 6.743 ms |
| `sd5` | 107.167 ms | 22.827 ms |
| `sd5_shift1` | 96.758 ms | 14.875 ms |
| `sd4_x_sd4shift1` | 24.875 ms | 10.683 ms |
| `xpow120_minus1` | 523.364 ms | 169.354 ms |
| `cyclo_phi64_x_phi105` | 87.946 ms | 38.511 ms |

## What Hex computes

The public function uses one direct-coordinate design:

1. normalize the polynomial once;
2. select and retain one modular prime plan in the original coordinates;
3. Hensel-lift and run bounded, size-ordered classical recombination;
4. when that search reaches its bound, pass the same modular plan to the
   direct-coordinate combined-logarithmic-derivative lattice method;
5. use exact trial division only when no suitable modular prime exists.

The classical iterator carries degree and trailing-residue information down
the subset tree. Before constructing a polynomial candidate, it checks the
necessary divisibility of the raw trailing coefficient. The Mathlib proof
relates this cached iterator to the extensional support enumeration and proves
that every genuine irreducible support survives the filter.

The remaining Swinnerton-Dyer cost is not duplicate work between coordinate
systems. For example, the selected modular image of `sd5` has sixteen factors,
and the irreducibility argument still examines 32,768 head-forced supports.
Useful future measurements should separate:

- modular prime selection, Hensel lifting, filter survivors, candidate
  construction, exact division, and lattice reduction;
- allocation and coefficient growth in the direct Hensel basis;
- logarithmic-derivative column count, lattice dimension, reduction
  iterations, and recovery precision.

These counters are needed before and after a proposed Swinnerton-Dyer or
cyclotomic optimization. Total wall time alone cannot distinguish a better
algorithm from a redistribution of the same work.

## Coverage and long tail

The 17 Hex timeouts are `cyclo_phi1031`; `sd7`, `sd6_shift1`, and
`sd6_shift5`; `sd5_x_sd5shift1`, `sd6_x_sd6shift1`, `sd6_x_phi13`, and
`sd6_x_phi105`; and nine of the ten Hoeij-Zimmermann rows:
`hoeij_P7`, `hoeij_F190`, `hoeij_F192`, `hoeij_F256`, `hoeij_F351`,
`hoeij_F630`, `hoeij_S7`, `hoeij_S8`, and `hoeij_S9`.

This coverage gap and the large difference from FLINT, PARI/GP, and NTL are
the main performance limitations after release.

## Six decision-useful graphs

1. [Balanced combined cactus plot](figures/hexbz-cactus-combined.svg)
2. [Chebyshev runtime versus degree](figures/hexbz-runtime-degree-chebyshev.svg)
3. [Legendre runtime versus degree](figures/hexbz-runtime-degree-legendre.svg)
4. [Swinnerton-Dyer runtime versus degree](figures/hexbz-runtime-degree-swinnerton-dyer.svg)
5. [Cyclotomic-product runtime versus degree](figures/hexbz-runtime-degree-cyclotomic-products.svg)
6. [Hoeij-Zimmermann runtime versus degree](figures/hexbz-runtime-degree-hoeij-zimmermann.svg)

The figures use the current public Hex record and the unchanged external
records. Superseded diagnostic implementations are not included.
