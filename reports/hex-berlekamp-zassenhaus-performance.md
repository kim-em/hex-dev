# HexBerlekampZassenhaus Performance Report

This report describes the supported public integer-polynomial factorization
entry point. Standalone classical and lattice entries remain development
diagnostics, not alternative public implementations.

## Current measurement

The current Hex record measures clean source revision
`4dc6bb16ae7e349b061ef9f2a55a95095f45ae56` with
`leanprover/lean4:v4.32.2`. The executable SHA-256 is
`ec2875103bb4e520947d952889df69df27805d10115e6ee2f24ed814c9098e47`.

All systems were measured on 2026-08-01 on `chungus2`, an AMD EPYC 9455 Linux
x86-64 host, with the harness and service pinned to CPU 0. The committed
392-row corpus has SHA-256
`619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`.
Services were persistent and warmed. Each call had a ten-second cutoff; rows
below one second used the median of five calls, and slower rows used one call.
Early termination was disabled.

The current artifacts are:

- `reports/bench-results/hexbz-factor-sweep-4dc6bb16-hex-chungus2.json`
  for Hex, SHA-256
  `bdaecbe3e7e384baf8d828b18d5d9de0c024e3fdfdb6848822b93222ebcc4fa5`;
- `reports/bench-results/hexbz-factor-sweep-aa68c920-chungus2.json`
  for FLINT, NTL, PARI, and both Isabelle implementations, SHA-256
  `4de27e389d738abc1e878f0be273485c3723216211a101c3eba55860e7b8a242`.

The second artifact contains an older same-run Hex row too, but the newer clean
Hex record supersedes it. The plotting and freshness tools select the newest
valid record independently for each system.

The prior PARI comparator artifact used PARI/GP 2.17.3; the current Nix closure
provided 2.17.2. No cross-record PARI change is attributed to Hex. All current
ratios and curves use the fresh same-protocol 2.17.2 measurement above.

## Cross-system result

| System | Answered | Timed out | Median | p90 | Slowest answer |
|---|---:|---:|---:|---:|---:|
| Hex public factorization | 376 | 16 | 372.713 us | 7.324 ms | 7.963 s |
| FLINT 0.9.0 | 391 | 1 | 60.089 us | 1.139 ms | 1.241 s |
| PARI/GP 2.17.2 | 391 | 1 | 65.687 us | 1.008 ms | 960.815 ms |
| NTL 11.6.0 | 391 | 1 | 88.160 us | 2.365 ms | 1.305 s |
| Verified Isabelle BZ | 371 | 21 | 439.591 us | 5.072 ms | 8.179 s |
| Verified Isabelle LLL | 314 | 78 | 6.036 ms | 1.210 s | 9.474 s |

Every answering system agreed with the committed factor-degree oracle or with
the other systems on rows without one.

For paired comparisons, both measurements must exceed ten times their own
protocol overhead. On 213 eligible common rows, Hex divided by verified
Isabelle BZ has median `0.746x`, p10-p90 `0.467x-2.621x`, and a 133-80 win
split. Hex therefore has a useful aggregate lead over verified Isabelle BZ,
but not a uniform one.

The optimized unverified libraries remain substantially faster. Median Hex
ratios are `10.730x` against FLINT, `11.919x` against PARI, and `5.746x`
against NTL on 74, 79, and 139 eligible pairs respectively.

## Effect of this optimization

The proposal path now has two general rules:

1. search support sizes one through three once, then repeatedly peel support
   sizes one or two from the exact quotient while reusing the same Hensel
   lift;
2. build a selected-coordinate proposal lattice only after peeling has made
   exact progress. With no peel, go directly to the exact full-CLD fallback.

These rules contain no family or benchmark names. They retain repeated cheap
progress on Wilkinson inputs and avoid speculative lattice work on inputs such
as `sd6` where the cheap search found nothing.

Against the preceding clean public record, 99 common rows above one
millisecond have median new/old `0.997x` and p10-p90
`0.978x-1.022x`; 56 are faster and 43 slower. Every family median lies between
`0.978x` and `1.014x`. The aggregate timed result is therefore neutral within
run-to-run noise across the existing corpus, while coverage improves by one.

Two hard rows make the benefit concrete:

- `hoeij_F190` is newly solved in 7.369 seconds after peeling a degree-10
  factor and partitioning the degree-180 residual into two degree-90 pieces;
- `sd6` answers in 7.963 seconds because a no-progress proposal now skips its
  futile selected-coordinate lattice. It had sat at or beyond the cutoff
  during the intermediate design.

Representative Wilkinson timings remain smooth: 4.036 ms at degree 24,
15.603 ms at degree 40, and 39.783 ms at degree 56. They are within about seven
percent of the preceding clean record, so the data supports absence of a new
threshold regression, not a Wilkinson speedup claim.

Both hard-row successes exceed one second and therefore use one timed call under
the declared repetition policy. F190 consumed 74% and `sd6` 80% of the ten-second
cutoff. They establish current coverage, but should be rechecked after future
factorization changes rather than treated as low-variance timing estimates.

## Relative to verified Isabelle BZ

| Family | Eligible pairs | Median Hex / Isabelle | Hex wins |
|---|---:|---:|---:|
| Chebyshev | 9 | 0.467x | 9 |
| Conway | 86 | 0.705x | 49 |
| Cyclotomic | 24 | 1.100x | 10 |
| Cyclotomic products | 18 | 1.050x | 9 |
| Laguerre | 13 | 0.766x | 12 |
| Legendre | 13 | 0.568x | 12 |
| Random products | 25 | 0.582x | 24 |
| Swinnerton-Dyer products | 7 | 0.769x | 4 |
| Swinnerton-Dyer | 6 | 2.801x | 3 |
| Wilkinson | 12 | 1.366x | 1 |

There is no common answered Hoeij-Zimmermann row with verified Isabelle BZ.
Hex is strong on Chebyshev, Legendre, random products, and Laguerre. Plain
Swinnerton-Dyer and Wilkinson remain the clearest verified-comparator gaps.

## Remaining long tail

The 16 Hex timeouts are `cyclo_phi1031`; `sd7`, `sd6_shift1`, and
`sd6_shift5`; `sd5_x_sd5shift1`, `sd6_x_sd6shift1`, `sd6_x_phi13`, and
`sd6_x_phi105`; and eight Hoeij-Zimmermann rows: `hoeij_P7`, `hoeij_F192`,
`hoeij_F256`, `hoeij_F351`, `hoeij_F630`, `hoeij_S7`, `hoeij_S8`, and
`hoeij_S9`.

The most promising next general optimization is to reuse all cached
other-prime degree-reachability bitsets inside classical recombination. The
planner already computes them, but the candidate iterator currently filters
only by the selected prime and target degree. Before implementation, record
per-level leaves, cross-prime degree survivors, constructed candidates, exact
divisions, and wall time; after implementation, require lower survivors and
candidate construction without a coverage loss or a material median
regression on the full corpus.
