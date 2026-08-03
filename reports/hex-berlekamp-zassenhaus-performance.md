# HexBerlekampZassenhaus Performance Report

This report describes the supported public integer-polynomial factorization
entry point. Standalone classical and lattice entries remain development
diagnostics, not alternative public implementations.

## Current measurement

The current Hex record measures clean source revision
`39b4d5ba1ca0cb2d59b51eb2f140b5d5d61e9cab` with
`leanprover/lean4:v4.33.0-rc1`.

Hex was measured on 2026-08-03 and the external systems on 2026-08-01 on
`chungus2`, an AMD EPYC 9455 Linux x86-64 host. The harness and service were
pinned to CPU 70 for the Hex record and to CPU 0 for the external one; the two
are checked interchangeable in
[hexbz-support-traversal.md](hexbz-support-traversal.md). The committed
392-row corpus has SHA-256
`619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`.
Services were persistent and warmed. Each call had a ten-second cutoff; rows
below one second used the median of five calls, and slower rows used one call.
Early termination was disabled.

The current artifacts are:

- `reports/bench-results/hexbz-factor-sweep-39b4d5ba-hex-chungus2.json`
  for Hex, SHA-256
  `9a2dbb2e4d92baedde8265f8bb2f730f5fc2f37a718000f7cbfbc0e445812b20`;
- `reports/bench-results/hexbz-factor-sweep-aa68c920-chungus2.json`
  for FLINT, NTL, PARI, and both Isabelle implementations, SHA-256
  `4de27e389d738abc1e878f0be273485c3723216211a101c3eba55860e7b8a242`.

The second artifact contains an older same-run Hex row too, but the clean Lean
4.33 Hex record supersedes it. The plotting and freshness tools select the
newest valid record independently for each system.

The prior PARI comparator artifact used PARI/GP 2.17.3; the current Nix closure
provided 2.17.2. No cross-record PARI change is attributed to Hex. All current
ratios and curves use the fresh same-protocol 2.17.2 measurement above.

## Cross-system result

| System | Answered | Timed out | Median | p90 | Slowest answer |
|---|---:|---:|---:|---:|---:|
| Hex public factorization | 377 | 15 | 380.464 us | 7.181 ms | 8.103 s |
| FLINT 0.9.0 | 391 | 1 | 60.089 us | 1.139 ms | 1.241 s |
| PARI/GP 2.17.2 | 391 | 1 | 65.687 us | 1.008 ms | 960.815 ms |
| NTL 11.6.0 | 391 | 1 | 88.160 us | 2.365 ms | 1.305 s |
| Verified Isabelle BZ | 371 | 21 | 439.591 us | 5.072 ms | 8.179 s |
| Verified Isabelle LLL | 314 | 78 | 6.036 ms | 1.210 s | 9.474 s |

Every answering system agreed with the committed factor-degree oracle or with
the other systems on rows without one.

For paired comparisons, both measurements must exceed ten times their own
protocol overhead. On 218 eligible common rows, Hex divided by verified
Isabelle BZ has median `0.734x`, p10-p90 `0.476x-2.588x`, and a 145-73 win
split. Hex therefore has a useful aggregate lead over verified Isabelle BZ,
but not a uniform one.

The optimized unverified libraries remain substantially faster. Median Hex
ratios are `10.563x` against FLINT, `10.795x` against PARI, and `5.542x`
against NTL on 75, 80, and 141 eligible pairs respectively.

## Effect of the divisibility obstruction

Between constructing a recombination candidate and dividing by it, the search
now reduces both modulo a fixed word-sized prime and rejects the candidate when
the finite-field remainder is nonzero. The filter can only reject; exact
integer division is still the only accepting test.

Across the profiled corpus, 4,204 of the 4,302 candidates reaching the filter
were rejected, and all 98 that passed were genuine divisors. `xpow120_minus1`
moves to 0.322x, `cyclo_phi275` to 0.238x, and `cyclo_phi1031` changes from a
ten-second timeout to 6.470 s; the aggregate of `xpow48/105/120` is 0.378x and
the whole corpus is 0.699x. The median over rows above one millisecond is
0.999x, and the cost side -- rows where nearly every candidate is a real
divisor -- has a median of 1.016x. The Swinnerton-Dyer families are flat,
because on them exact division was never the cost; against verified Isabelle BZ
this revision's `cyclotomic` median is `0.914x` and `cyclotomic-products`
`0.859x`.

Those ratios are measured against this branch's merge base, built and swept in
the same session, not against the previous committed record: `main` moved
between the two, and rows this change cannot touch move more against that
record than rows it can.
[hexbz-modular-obstruction.md](hexbz-modular-obstruction.md) is the measurement
record, and it also states what the change does not fix.

## Effect of the support-traversal change

The head-forced recombination leaf now runs its metadata-only filters before
it materializes anything, and the lift modulus and per-factor degree and
trailing coefficient are precomputed once per subset-cardinality level. The
Swinnerton-Dyer family moves from 0.684x to 0.850x against the preceding
record, and its median against verified Isabelle BZ improves from `2.799x` to
`2.116x`. No other family moves more than 3%.
[hexbz-support-traversal.md](hexbz-support-traversal.md) is the measurement
record.

## Effect of the earlier proposal-path optimization

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
millisecond have median new/old `1.017x` and p10-p90
`0.992x-1.043x`; 19 are faster and 80 slower. Every family median lies between
`0.991x` and `1.035x`. This final comparison includes the intervening Lean 4.33
toolchain and core-library update; it shows a small broad slowdown rather than
an optimization-only effect, while coverage improves by one.

Two hard rows make the benefit concrete:

- `hoeij_F190` is newly solved in 6.862 seconds after peeling a degree-10
  factor and partitioning the degree-180 residual into two degree-90 pieces;
- `sd6` answers in 8.367 seconds because a no-progress proposal now skips its
  futile selected-coordinate lattice. It had sat at or beyond the cutoff
  during the intermediate design.

Representative Wilkinson timings remain smooth: 4.098 ms at degree 24,
15.679 ms at degree 40, and 39.740 ms at degree 56. They are within about seven
percent of the preceding clean record, so the data supports absence of a new
threshold regression, not a Wilkinson speedup claim.

Both hard-row successes exceed one second and therefore use one timed call under
the declared repetition policy. F190 consumed 69% and `sd6` 84% of the ten-second
cutoff. They establish current coverage, but should be rechecked after future
factorization changes rather than treated as low-variance timing estimates.

## Relative to verified Isabelle BZ

| Family | Eligible pairs | Median Hex / Isabelle | Hex wins |
|---|---:|---:|---:|
| Chebyshev | 9 | 0.467x | 9 |
| Conway | 87 | 0.707x | 50 |
| Cyclotomic | 24 | 1.085x | 11 |
| Cyclotomic products | 18 | 1.044x | 9 |
| Laguerre | 13 | 0.773x | 13 |
| Legendre | 13 | 0.575x | 12 |
| Random products | 25 | 0.584x | 24 |
| Swinnerton-Dyer products | 7 | 0.766x | 4 |
| Swinnerton-Dyer | 6 | 2.116x | 3 |
| Wilkinson | 12 | 1.403x | 0 |

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

## Where the mid-tail time goes

[`hexbz-cactus-elbow.md`](hexbz-cactus-elbow.md) is the phase-attributed
record for the solved-rank 125-140 region where verified Isabelle BZ overtakes
Hex on the combined cactus. It carries the per-phase table, the counterfactual
prime plans, exact ranks 118-144 in both the cumulative and paired readings,
and the symbolized sampling profiles.
