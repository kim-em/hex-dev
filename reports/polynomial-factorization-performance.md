# Polynomial Factorization Performance

This is the current cross-system snapshot for the supported integer
polynomial factorization function. It compares the public Hex implementation
with three optimized external libraries and two verified Isabelle
implementations.

## Result at a glance

| System | Answered / 392 | Median solved time | p90 solved time |
|---|---:|---:|---:|
| Hex factorization | 376 | 378.276 us | 7.507 ms |
| FLINT | 391 | 60.089 us | 1.139 ms |
| PARI/GP | 391 | 65.687 us | 1.008 ms |
| NTL | 391 | 88.160 us | 2.365 ms |
| Verified Isabelle BZ | 371 | 439.591 us | 5.072 ms |
| Verified Isabelle LLL | 314 | 6.036 ms | 1.210 s |

Hex is faster than verified Isabelle BZ in aggregate, while FLINT, PARI, and
NTL remain substantially faster and cover almost the whole corpus. Hex has a
sub-millisecond median but a pronounced multi-second tail.

Every pair of answering systems agreed on factor degrees. Timings come from
fresh 2026-08-01/02 measurements on the same host, corpus, CPU placement,
cutoff, and repetition policy. See
[`hexbz-factor-sweep.md`](hexbz-factor-sweep.md) for exact provenance, and
[`hexbz-cactus-elbow.md`](hexbz-cactus-elbow.md) for the phase-by-phase
attribution of the mid-tail crossover with verified Isabelle BZ.

## Paired comparisons

A row is eligible only when both timings exceed ten times their own measured
protocol overhead. A ratio below one favors Hex.

| Hex / comparator | Eligible pairs | Median | p10-p90 | Hex wins |
|---|---:|---:|---:|---:|
| FLINT | 74 | 11.056x | 4.413x-100.350x | 0 |
| PARI/GP | 79 | 12.029x | 2.699x-107.045x | 0 |
| NTL | 140 | 5.923x | 1.189x-36.847x | 8 |
| Verified Isabelle BZ | 216 | 0.754x | 0.467x-2.713x | 134 |
| Verified Isabelle LLL | 166 | 0.00806x | 0.000281x-0.226x | 165 |

The broad percentile bands matter: performance depends strongly on the
polynomial family, so none of these medians is a uniform ordering.

## What changed

The current path reuses one Hensel lift for repeated exact low-cardinality
peeling. It builds the small selected-coordinate CLD lattice only after peeling
has produced an exact factor; otherwise it goes directly to the exact full-CLD
fallback. Every proposed piece is reconstructed exactly and refactored by the
proved classical engine.

This gives a general rather than family-specific result. On 99 common rows
above one millisecond versus the preceding clean record, median new/old is
`1.017x`, with p10-p90 `0.992x-1.043x`; every family median is within about 4%
of parity. This comparison includes the Lean 4.33 toolchain and core-library
update, so it describes the final shipped state rather than isolating the
optimization. Coverage increases by one with no lost row:

- `hoeij_F190`: 7.238 s, newly solved;
- `sd6`: 8.115 s, retained at 81% of the cutoff;
- Wilkinson degrees 24, 40, and 56: 4.083 ms, 15.912 ms, and 40.396 ms.

F190 and `sd6` each use one timed call because they exceed one second. These are
coverage observations, not low-variance speed estimates. The Wilkinson points
are within about seven percent of the preceding clean record; they show that the
general change did not introduce a new threshold regression, not a speedup.

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
