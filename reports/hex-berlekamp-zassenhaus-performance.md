# HexBerlekampZassenhaus Performance Report

This report describes the supported public integer-polynomial factorization
entry point. Standalone classical and lattice entries remain development
diagnostics, not alternative public implementations.

## Current measurement

The current Hex record measures clean source revision
`acb930159913e8e6c04a271e4e9aa0d227ea0e7b` with
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

- `reports/bench-results/hexbz-factor-sweep-acb93015-hex-chungus2.json`
  for Hex, SHA-256
  `42b69d970e0cba7336091b16e512d89e9aed4383bdb661edbd6cc97e96f56138`;
- `reports/bench-results/hexbz-factor-sweep-aa68c920-chungus2.json`
  for FLINT, NTL, PARI, and both Isabelle implementations, SHA-256
  `4de27e389d738abc1e878f0be273485c3723216211a101c3eba55860e7b8a242`;
- `reports/bench-results/hexbz-factor-sweep-04107b17-hex-chungus2.json`,
  SHA-256
  `b4f923078d3ac66482da91a646780d939bbc1cd656259ba912d197779952c94d`,
  is a clean intermediate Hex repeatability record. It independently records
  the F190 result but is older than the final Hex artifact and is not selected
  for the current plots.

The second artifact contains a same-run Hex row too, but the newer clean Hex
record supersedes it after a repeatability check found transient host
contention in that row. The plotting and freshness tools select the newest
valid record independently for each system.

The prior PARI comparator artifact used PARI/GP 2.17.3; the current Nix closure
provided 2.17.2. No cross-record PARI change is attributed to Hex. All current
ratios and curves use the fresh same-protocol 2.17.2 measurement above.

## Cross-system result

| System | Answered | Timed out | Median | p90 | Slowest answer |
|---|---:|---:|---:|---:|---:|
| Hex public factorization | 376 | 16 | 367.114 us | 7.503 ms | 7.866 s |
| FLINT 0.9.0 | 391 | 1 | 60.089 us | 1.139 ms | 1.241 s |
| PARI/GP 2.17.2 | 391 | 1 | 65.687 us | 1.008 ms | 960.815 ms |
| NTL 11.6.0 | 391 | 1 | 88.160 us | 2.365 ms | 1.305 s |
| Verified Isabelle BZ | 371 | 21 | 439.591 us | 5.072 ms | 8.179 s |
| Verified Isabelle LLL | 314 | 78 | 6.036 ms | 1.210 s | 9.474 s |

Every answering system agreed with the committed factor-degree oracle or with
the other systems on rows without one.

For paired comparisons, both measurements must exceed ten times their own
protocol overhead. On 216 eligible common rows, Hex divided by verified
Isabelle BZ has median `0.729x`, p10-p90 `0.462x-2.610x`, and a 138-78 win
split. Hex therefore has a useful aggregate lead over verified Isabelle BZ,
but not a uniform one.

The optimized unverified libraries remain substantially faster. Median Hex
ratios are `10.735x` against FLINT, `11.726x` against PARI, and `5.683x`
against NTL on 74, 79, and 140 eligible pairs respectively.

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

Against the preceding clean public record, 98 common rows above one
millisecond have median new/old `0.995x` and p10-p90
`0.973x-1.026x`; 59 are faster and 39 slower. Every family median lies between
`0.973x` and `1.014x`. The aggregate timed result is therefore neutral within
run-to-run noise across the existing corpus, while coverage improves by one.

Two hard rows make the benefit concrete:

- `hoeij_F190` is newly solved in 7.215 seconds after peeling a degree-10
  factor and partitioning the degree-180 residual into two degree-90 pieces;
- `sd6` answers in 7.866 seconds because a no-progress proposal now skips its
  futile selected-coordinate lattice. It had sat at or beyond the cutoff
  during the intermediate design.

Representative Wilkinson timings remain smooth: 3.992 ms at degree 24,
15.666 ms at degree 40, and 39.963 ms at degree 56. They are within about five
percent of the preceding clean record, so the data supports absence of a new
threshold regression, not a Wilkinson speedup claim.

Both hard-row successes exceed one second and therefore use one timed call under
the declared repetition policy. F190 consumed 72% and `sd6` 79% of the ten-second
cutoff. They establish current coverage, but should be rechecked after future
factorization changes rather than treated as low-variance timing estimates.

## Relative to verified Isabelle BZ

| Family | Eligible pairs | Median Hex / Isabelle | Hex wins |
|---|---:|---:|---:|
| Chebyshev | 9 | 0.466x | 9 |
| Conway | 88 | 0.712x | 50 |
| Cyclotomic | 24 | 1.066x | 12 |
| Cyclotomic products | 18 | 1.046x | 9 |
| Laguerre | 13 | 0.762x | 13 |
| Legendre | 13 | 0.566x | 12 |
| Random products | 26 | 0.576x | 25 |
| Swinnerton-Dyer products | 7 | 0.764x | 4 |
| Swinnerton-Dyer | 6 | 2.748x | 3 |
| Wilkinson | 12 | 1.362x | 1 |

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
