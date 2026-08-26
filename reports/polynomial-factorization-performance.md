# Polynomial Factorization Performance

This is the current cross-system snapshot for the supported integer
polynomial factorization function. It compares the public Hex implementation
with three optimized external libraries and two verified Isabelle
implementations.

## Result at a glance

| System | Answered / 392 | Median solved time | p90 solved time |
|---|---:|---:|---:|
| Hex factorization | 383 | 273.175 us | 6.693 ms |
| FLINT | 391 | 60.089 us | 1.139 ms |
| PARI/GP | 391 | 65.687 us | 1.008 ms |
| NTL | 391 | 88.160 us | 2.365 ms |
| Verified Isabelle BZ | 371 | 439.591 us | 5.072 ms |
| Verified Isabelle LLL | 314 | 6.036 ms | 1.210 s |

Hex is faster than verified Isabelle BZ in aggregate and solves ten more rows
on the balanced combined mixture, while FLINT, PARI, and NTL remain
substantially faster and cover almost the whole corpus. Hex has a
sub-millisecond median but a pronounced multi-second tail.

Every pair of answering systems agreed on factor degrees. Timings come from
fresh 2026-08-01/10 measurements on the same host and corpus, with each service
pinned to one core, the same cutoff, and the same repetition policy. See
[`hexbz-factor-sweep.md`](hexbz-factor-sweep.md) for exact provenance, and
[`hexbz-quadratic-norm-certificate.md`](hexbz-quadratic-norm-certificate.md)
for the phase-by-phase account of how the former mid-tail crossover with
verified Isabelle BZ was removed.

## Paired comparisons

A row is eligible only when both timings exceed ten times their own measured
protocol overhead. A ratio below one favors Hex.

| Hex / comparator | Eligible pairs | Median | p10-p90 | Hex wins |
|---|---:|---:|---:|---:|
| FLINT | 80 | 6.493x | 2.474x-22.967x | 1 |
| PARI/GP | 86 | 6.316x | 2.049x-48.730x | 0 |
| NTL | 142 | 3.020x | 1.039x-11.787x | 14 |
| Verified Isabelle BZ | 189 | 0.506x | 0.316x-1.525x | 153 |
| Verified Isabelle LLL | 137 | 0.00527x | 0.000169x-0.166x | 137 |

The broad percentile bands matter: performance depends strongly on the
polynomial family, so none of these medians is a uniform ordering.

## What changed

The current path reuses one Hensel lift for repeated exact low-cardinality
peeling. It builds the small selected-coordinate CLD lattice only after peeling
has produced an exact factor; otherwise it goes directly to the exact full-CLD
fallback. Every proposed piece is reconstructed exactly and refactored by the
proved classical engine.

The path also carries a proved iterated-quadratic-norm certificate for the
multiquadratic irreducible class. It removes the exponential recombination tail
on plain Swinnerton-Dyer inputs without a benchmark-name or family dispatch.
On the balanced 160-row mixture Hex now solves 151 rows against verified
Isabelle BZ's 141; its worst cumulative Hex/Isabelle ratio over ranks 125-140 is
`0.689x` at rank 133.

Current representative rows are:

- `hoeij_F190`: 3.287 s, one timed call;
- `sd6`: 27.044 ms, the median of five calls;
- Wilkinson degrees 24, 40, and 56: 3.480 ms, 9.431 ms, and 21.266 ms.

These are current coverage observations, not an optimization-only A/B.

The remaining gap is still large. For example, NTL takes 35.224 ms on
`hoeij_F190`, and FLINT, PARI, and NTL all solve 391 rows.

## Six decision-useful graphs

1. [Balanced combined cactus plot](figures/hexbz-cactus-combined.svg)
2. [Chebyshev runtime versus degree](figures/hexbz-runtime-degree-chebyshev.svg)
3. [Legendre runtime versus degree](figures/hexbz-runtime-degree-legendre.svg)
4. [Swinnerton-Dyer runtime versus degree](figures/hexbz-runtime-degree-swinnerton-dyer.svg)
5. [Cyclotomic-product runtime versus degree](figures/hexbz-runtime-degree-cyclotomic-products.svg)
6. [Hoeij-Zimmermann runtime versus degree](figures/hexbz-runtime-degree-hoeij-zimmermann.svg)

All 25 cactus and runtime-by-degree SVGs under `reports/figures/hexbz-*` were
regenerated from the current artifacts. CI now checks both measurement
freshness and byte-for-byte plot regeneration on every PR.
