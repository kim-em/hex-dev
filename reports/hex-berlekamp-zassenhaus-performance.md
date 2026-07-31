# HexBerlekampZassenhaus Performance Report

This report describes the supported public integer-factorization entry point.
Standalone classical and lattice entries remain useful development diagnostics,
but they are not presented as alternative public implementations.

## Measurement

The Hex record measures clean source revision
`75291ae2fe6c58d95ba73dff9e5d2720df11b3d5` with
`leanprover/lean4:v4.32.2`.  The executable SHA-256 is
`f1b2c4262493cc35c68b2c433bba3803d31f6a27631000f52a6ee295721a6fe4`.

The sweep ran on `chungus2`, an AMD EPYC 9455 Linux x86-64 host, with the
harness and service pinned to CPU 0.  It used the committed 392-row corpus
`bench/corpus/hexbz-factor-corpus.jsonl`, whose SHA-256 is
`619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`.
Each service is persistent and warmed before measurement.  The harness uses a
ten-second cutoff per call, the median of five calls when the first call is
under one second, and one call otherwise.  Early termination was disabled.
The public Hex protocol floor was 20.120 microseconds.

The durable Hex record is
`reports/bench-results/hexbz-factor-sweep-75291ae2-chungus2.json`
(SHA-256
`5d8b08225a4f2a0c8288d9f536303193a2f54b312a1cbae57ffcac23cd6295bd`).
It records the full source revision, clean-worktree flag, toolchain, corpus
hash, host, cutoff, repetition policy, and protocol overhead.

The FLINT, PARI/GP, NTL, and verified Isabelle records are the unchanged
2026-07-28 measurements from the same host, corpus, CPU placement, cutoff, and
protocol.  They were not rerun because none of those inputs changed.

## Cross-system results

| System | Answered | Timed out | Median among answered rows |
|---|---:|---:|---:|
| Hex public factorization | 375 | 17 | 352.262 µs |
| FLINT 0.9.0 | 391 | 1 | 66.850 µs |
| PARI/GP 2.17.3 | 391 | 1 | 99.958 µs |
| NTL 11.6.0 | 391 | 1 | 135.631 µs |
| Verified Isabelle BZ | 371 | 21 | 441.134 µs |
| Verified Isabelle LLL | 314 | 78 | 6.109 ms |

Every pair of systems that answered agreed on the multiset of factor degrees.
The coverage count treats every timeout as unsolved; it does not discard hard
rows.

For comparisons below, a pair is eligible only when both measurements exceed
ten times their own service's protocol floor.  On the 218 eligible common rows,
Hex divided by verified Isabelle Berlekamp-Zassenhaus has median `0.734×` and
10th-to-90th percentile range `0.460×` to `2.552×`.  Hex wins 137 rows and
Isabelle wins 81.  Thus Hex has a useful aggregate lead, but the broad range
does not support a claim of uniform superiority.

The optimized unverified libraries remain substantially faster.  Hex/FLINT has
median `11.68×` on 64 eligible rows, Hex/PARI has median `7.65×` on 81, and
Hex/NTL has median `4.36×` on 170.  Hex wins none of the eligible FLINT or PARI
pairs and 17 of the NTL pairs.

## Families relative to verified Isabelle BZ

| Corpus family | Eligible pairs | Median Hex / Isabelle | Hex wins |
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

Hoeij-Zimmermann has no common answered row with verified Isabelle BZ, so it
has no eligible family comparison.

The stable build is particularly strong on the Chebyshev and Legendre rows
that motivated the direct-coordinate lifting work.  The remaining weak
families are plain Swinnerton-Dyer, Wilkinson, and parts of the cyclotomic
families.

## Coverage and long tail

Hex solves every Chebyshev, Conway, cyclotomic-product, Laguerre, Legendre,
random-product, and Wilkinson row.  The 17 cutoff rows are:

- `cyclo_phi1031`;
- `sd7`, `sd6_shift1`, and `sd6_shift5`;
- `sd5_x_sd5shift1`, `sd6_x_sd6shift1`, `sd6_x_phi13`, and `sd6_x_phi105`;
- `hoeij_P7`, `hoeij_F190`, `hoeij_F192`, `hoeij_F256`, `hoeij_F351`,
  `hoeij_F630`, `hoeij_S7`, `hoeij_S8`, and `hoeij_S9`.

The Hoeij-Zimmermann family is the largest coverage gap: one of ten rows
answers within the cutoff.  Swinnerton-Dyer products solve ten of fourteen,
plain Swinnerton-Dyer solves twelve of fifteen, and cyclotomic solves
thirty-three of thirty-four.  These failures, together with the large gap to
FLINT, PARI, and NTL, are the main performance work remaining after release.

The regenerated cactus and runtime-by-degree figures under `reports/figures/`
merge this Hex record with the unchanged external records.  The plotting tool
checks the common corpus hash before combining them and identifies the exact
source artifact used for each system.
