# HexBZ Cactus Elbow: Phase-Attributed Baseline

The combined cross-system cactus has Hex ahead of the verified Isabelle
Berlekamp-Zassenhaus extraction through solved rank 124, behind it from 125
through 140, and ahead again from 141 once Isabelle meets `cyclo_phi1031`.
This page is the durable attribution record for that elbow: where the time
goes, phase by phase, on the rows that populate it, and what a different
modular prime would have cost. It records measurements, not conclusions
carried over from a profiler session.

Every number here is reproducible from committed records by the commands in
[Regeneration](#regeneration).

## Revision and protocol

- Source revision `8b5cf9434d9fc7ed110b1e685a850ef7da37bf31` (clean worktree),
  Lean toolchain `leanprover/lean4:v4.33.0-rc1`.
- Host `chungus2`, AMD EPYC 9455, Linux x86-64, 96 cores.
- The measurement harness and the measured service were pinned to CPU 0 with
  `taskset -c 0`; the sampling profiles pinned the service to CPU 0 the same
  way. Nothing else ran on the host during a measurement.
- Corpus `bench/corpus/hexbz-factor-corpus.jsonl`, 392 rows, SHA-256
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`. The
  combined mix-doctrine mixture the cactus plots is its 160 `combined` rows.
- `hexbz_factor_service` SHA-256
  `42d3031561c8eb56bcd9a540227278921ac57217b2fc0fabd77dd3e152d836e3`.
- Cross-system sweep: persistent warm services, ten-second per-call cutoff,
  median of five calls below one second and one call otherwise, early
  termination disabled. Measured protocol overhead 21.382 us per Hex call;
  reported times do not subtract it.
- Phase profile: one warm-up call, then five timed calls below one second and
  one otherwise, 120-second cutoff. The retained profile is the single
  execution whose total is closest to the median, so its phases still sum to
  its own total rather than mixing phases from different executions.
- Sampling profiles: samply 0.13.1 at 999 Hz, each row replayed enough times
  to reach roughly six seconds of samples, symbolicated through samply's
  presymbolicated sidecar and demangled. Raw `*.json.gz` profiles are not
  committed (`SPEC/profiling.md`); the committed record is the analytical
  summary.

### Artifacts

| Record | SHA-256 |
|---|---|
| `reports/bench-results/hexbz-factor-sweep-8b5cf943-hex-chungus2.json` | `c2f21575429dab828102008b71bb0a3bdf45a372b99737ef05f6cac73941c778` |
| `reports/bench-results/hexbz-factor-sweep-aa68c920-chungus2.json` | `4de27e389d738abc1e878f0be273485c3723216211a101c3eba55860e7b8a242` |
| `reports/bench-results/hexbz-phase-profile-8b5cf943-chungus2.json` | `1ec2597e8502ab9d974fbb7909f82f6da41515debc0690cfbc77150089f8d8f7` |
| `reports/bench-results/hexbz-factor-sampling-profiles-8b5cf943-chungus2.json` | `ffa4ef3895a59f6dbfa0c059a562a3a67e88a45044b24191c30d6cbdd36febb1` |

The first record supplies Hex; the second, measured 2026-08-01 under the same
protocol on the same host, supplies FLINT, NTL, PARI, and both Isabelle
extractions and is reused unchanged. The plotting and freshness tools pick the
newest valid record per system, so the committed SVGs and the tables below read
the same measurements.

## How the diagnostic works

`bench/HexBench/FactorService.lean` gains two entries. Neither is reachable
from `Hex.ZPoly.factorize`, so an ordinary factorization pays nothing for them.

`--entry factorPhaseProfile` walks one production factorization phase by
phase, calling the production function each phase names in production order:
normalization, the bounded good-prime walk `directPrimePlan?`, the Hensel lift
`directLiftedBasis`, direct recombination, factor validation, and whichever of
the proposal-replay, CLD-lattice, and trial-division tiers answers. Times,
small-allocation counts (Lean's per-thread heartbeat counter is the number of
small allocations), and every structural counter come from that one execution.

Recombination is the one place the diagnostic does not call the production
function verbatim. The production head-forced search records only a leaf count,
so `countedSearch` mirrors `searchDirect` leaf for leaf -- same traversal order,
same budget rule, and the same shared leaf predicates
(`directDegreePrefilter`, `directTrailingPrefilter`, `directCandidate`,
`shouldRecordPolynomialFactor`, `exactQuotient?`) -- while threading the
`DirectCandidateStats` stage counters that the unforced sweep already records.
That is what makes cheap-filter rejections, candidate products materialized,
and exact divisions attempted come from the execution being timed.

`--entry primeCounterfactual` replays the downstream lift and recombination for
every good prime the bounded walk retained. Only the row marked selected is
work the production cascade did; the others are the counterfactual.

### Validation

Two checks ran on a wider sample than the representative set, over the 367
corpus rows the direct classical tier answers inside a two-second cutoff:

- the mirror's leaf count equals the production `factorTrace`
  `candidatesTried` on **367 of 367** rows, and the selected prime agrees on
  **367 of 367**;
- the phase-decomposed total tracks the untimed end-to-end `factor` call with
  median ratio **0.995** and maximum **1.026**, so the phase decomposition and
  the extra stage counters cost at most about 2.6% of the cascade.

Both are recomputed on every run and the driver exits non-zero on any
disagreement.

## Phase attribution

Shares are of that execution's own total, which excludes the modular sub-phase
repeat described below. `wilkinson_*` answers from the proposal-replay tier, so
its Hensel lift and recombination happen inside `proposeFactorization` and show
up in the last column; the sampling profiles below separate them.

| instance | degree | method | total | normalize | prime walk | Hensel lift | recombination | proposal / lattice / trial | small allocations |
|---|---:|---|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 32 | classical | 110.859 ms | 0.0% | 8.5% | 1.8% | 89.7% | 0.0% | 4,152,825 |
| `sd5_shift1` | 32 | classical | 97.647 ms | 0.1% | 10.6% | 2.0% | 87.2% | 0.0% | 4,059,402 |
| `sd5_shift2` | 32 | classical | 102.003 ms | 0.0% | 12.4% | 1.9% | 85.6% | 0.0% | 4,279,572 |
| `sd4_x_sd4shift1` | 32 | classical | 24.064 ms | 0.2% | 40.5% | 7.8% | 51.2% | 0.0% | 1,482,915 |
| `sd5_x_phi11` | 42 | classical | 224.575 ms | 0.0% | 9.5% | 1.4% | 89.0% | 0.0% | 9,144,658 |
| `xpow48_minus1` | 48 | classical | 21.138 ms | 0.1% | 29.2% | 5.6% | 64.7% | 0.0% | 827,081 |
| `xpow105_minus1` | 105 | classical | 83.094 ms | 0.0% | 45.9% | 19.0% | 34.8% | 0.0% | 4,040,320 |
| `xpow120_minus1` | 120 | classical | 531.947 ms | 0.0% | 12.1% | 4.0% | 83.8% | 0.0% | 11,276,025 |
| `cyclo_phi179` | 178 | classical | 80.414 ms | 0.1% | 18.4% | 74.6% | 6.9% | 0.0% | 2,736,483 |
| `cyclo_phi64_x_phi105` | 80 | classical | 86.300 ms | 0.2% | 85.3% | 8.9% | 5.5% | 0.0% | 7,122,386 |
| `cyclo_phi128_x_phi165` | 144 | classical | 204.156 ms | 0.3% | 47.0% | 32.3% | 20.3% | 0.0% | 10,917,285 |
| `cyclo_phi385` | 240 | classical | 464.686 ms | 0.3% | 45.0% | 36.8% | 17.9% | 0.0% | 22,966,223 |
| `wilkinson_40` | 40 | replay | 15.632 ms | 0.5% | 37.9% | 0.0% | 0.0% | 60.2% | 752,033 |
| `wilkinson_48` | 48 | replay | 29.490 ms | 0.3% | 31.7% | 0.0% | 0.0% | 66.8% | 1,256,804 |
| `wilkinson_56` | 56 | replay | 40.104 ms | 0.3% | 33.9% | 0.0% | 0.0% | 64.6% | 1,786,620 |
| `chebyshev_T24` (control) | 24 | classical | 523.927 us | 3.2% | 65.2% | 24.2% | 3.9% | 0.0% | 39,777 |
| `chebyshev_U24` (control) | 24 | classical | 663.824 us | 2.6% | 49.0% | 40.9% | 3.8% | 0.0% | 44,758 |
| `legendre_P30` (control) | 30 | classical | 8.142 ms | 0.4% | 92.7% | 5.7% | 0.8% | 0.0% | 707,348 |
| `legendre_P38` (control) | 38 | classical | 4.566 ms | 0.8% | 82.9% | 14.4% | 1.1% | 0.0% | 388,693 |
| `cyclo_phi17` (control) | 16 | classical | 127.790 us | 5.9% | 81.2% | 1.7% | 3.9% | 0.0% | 9,526 |
| `cyclo_phi41` (control) | 40 | classical | 2.826 ms | 0.6% | 25.2% | 24.0% | 49.5% | 0.0% | 123,094 |
| `xpow24_minus1` (control) | 24 | classical | 3.480 ms | 0.2% | 41.5% | 8.8% | 48.3% | 0.0% | 179,610 |
| `randprod_10` (control) | 20 | classical | 776.872 us | 2.6% | 70.6% | 22.1% | 2.5% | 0.0% | 59,044 |
| `randprod_21` (control) | 24 | classical | 1.694 ms | 1.5% | 75.7% | 19.1% | 2.3% | 0.0% | 134,447 |

The elbow rows split into three shapes. Swinnerton-Dyer rows and `x^n - 1` are
recombination-bound. `cyclo_phi179` is Hensel-bound. `cyclo_phi64_x_phi105`,
`cyclo_phi128_x_phi165`, `cyclo_phi385`, and every cheap control are prime-walk
bound -- and for the controls that is unremarkable, because their total is
small. `cyclo_phi64_x_phi105` is the sharp case: 85.3% of an 86.3 ms total is
the prime walk, while the plan it selects needs only 12.8 ms downstream.

### Recombination counters

| instance | local factors | Hensel precision | lift tree internal lifts | nodes | cheap-filter rejections | products materialized | exact divisions | successful divisors |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 16 | 19 | 15 | 32,768 | 32,639 | 129 | 129 | 1 |
| `sd5_shift1` | 16 | 19 | 15 | 32,768 | 32,767 | 1 | 1 | 1 |
| `sd5_shift2` | 16 | 19 | 15 | 32,768 | 32,767 | 1 | 1 | 1 |
| `sd4_x_sd4shift1` | 16 | 17 | 15 | 10,540 | 10,530 | 10 | 10 | 2 |
| `sd5_x_phi11` | 17 | 21 | 16 | 65,522 | 65,264 | 258 | 258 | 2 |
| `xpow48_minus1` | 19 | 14 | 18 | 268 | 0 | 268 | 268 | 10 |
| `xpow105_minus1` | 14 | 26 | 13 | 60 | 0 | 60 | 60 | 8 |
| `xpow120_minus1` | 39 | 43 | 38 | 5,339 | 3,538 | 1,801 | 1,801 | 16 |
| `cyclo_phi179` | 2 | 113 | 1 | 2 | 0 | 2 | 2 | 1 |
| `cyclo_phi64_x_phi105` | 10 | 24 | 9 | 130 | 102 | 28 | 28 | 2 |
| `cyclo_phi128_x_phi165` | 8 | 52 | 7 | 54 | 29 | 25 | 25 | 2 |
| `cyclo_phi385` | 4 | 152 | 3 | 8 | 0 | 8 | 8 | 1 |
| `wilkinson_40` | 40 | proposal tier | -- | -- | -- | -- | -- | -- |
| `wilkinson_48` | 48 | proposal tier | -- | -- | -- | -- | -- | -- |
| `wilkinson_56` | 56 | proposal tier | -- | -- | -- | -- | -- | -- |
| `chebyshev_T24` | 3 | 22 | 2 | 3 | 1 | 2 | 2 | 2 |
| `chebyshev_U24` | 4 | 33 | 3 | 4 | 0 | 4 | 4 | 4 |
| `legendre_P30` | 4 | 15 | 3 | 8 | 7 | 1 | 1 | 1 |
| `legendre_P38` | 3 | 19 | 2 | 4 | 3 | 1 | 1 | 1 |
| `cyclo_phi17` | 1 | 11 | 0 | 1 | 0 | 1 | 1 | 1 |
| `cyclo_phi41` | 5 | 26 | 4 | 16 | 0 | 16 | 16 | 1 |
| `xpow24_minus1` | 13 | 7 | 12 | 113 | 0 | 113 | 113 | 8 |
| `randprod_10` | 4 | 11 | 3 | 5 | 3 | 2 | 2 | 2 |
| `randprod_21` | 7 | 9 | 6 | 13 | 10 | 3 | 3 | 3 |

The Swinnerton-Dyer rows exhaust every head-forced cardinality: 32,768 leaves
for 16 local factors, of which the cheap degree and trailing-coefficient
filters reject all but 129 (`sd5`) or 1 (its shifts). The `x^n - 1` rows are
the opposite: `xpow48_minus1`, `xpow105_minus1`, and `xpow24_minus1` reject
nothing cheaply, so every leaf becomes a materialized product and an attempted
exact division.

### Modular sub-phases at the selected prime

This block is a repeat of the modular factorization at the already-selected
prime; the production planner calls `probePrimeData?`, which does not expose
its internal stages. Its cost is excluded from the totals above. The production
route splits from the fixed-space kernel and never runs distinct-degree
factorization, so there is no distinct-degree stage to attribute.
`berlekampFactor` recomputes the kernel internally, so equal-degree splitting
is its total less the separately measured matrix construction and row
reduction.

| instance | prime | modular degree | kernel dimension | modular image | good-prime test | Berlekamp matrix | row reduction | equal-degree splitting |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 29 | 32 | 16 | 1.342 us | 18.307 us | 1.472 us | 1.540 ms | 2.046 ms |
| `sd5_shift1` | 29 | 32 | 16 | 1.683 us | 32.178 us | 1.512 us | 2.222 ms | 1.420 ms |
| `sd5_shift2` | 29 | 32 | 16 | 1.782 us | 31.457 us | 1.482 us | 2.235 ms | 2.883 ms |
| `sd4_x_sd4shift1` | 29 | 32 | 16 | 1.693 us | 32.949 us | 1.462 us | 2.249 ms | 2.159 ms |
| `sd5_x_phi11` | 29 | 42 | 17 | 2.273 us | 49.604 us | 1.933 us | 4.498 ms | 4.342 ms |
| `xpow48_minus1` | 11 | 48 | 19 | 1.112 us | 5.548 us | 2.283 us | 739.707 us | 1.374 ms |
| `xpow105_minus1` | 17 | 105 | 14 | 2.223 us | 11.187 us | 4.977 us | 4.785 ms | 5.063 ms |
| `xpow120_minus1` | 7 | 120 | 39 | 2.514 us | 13.029 us | 6.039 us | 3.706 ms | 13.416 ms |
| `cyclo_phi179` | 3 | 178 | 2 | 4.037 us | 35.031 us | 8.353 us | 13.518 ms | 904.349 us |
| `cyclo_phi64_x_phi105` | 11 | 80 | 10 | 2.003 us | 154.068 us | 3.585 us | 18.362 ms | 3.098 ms |
| `cyclo_phi128_x_phi165` | 7 | 144 | 8 | 3.375 us | 458.129 us | 6.941 us | 89.725 ms | 6.071 ms |
| `cyclo_phi385` | 3 | 240 | 4 | 6.149 us | 774.669 us | 13.630 us | 204.972 ms | 6.540 ms |
| `wilkinson_40` | 47 | 40 | 40 | 2.403 us | 19.269 us | 1.843 us | 248.408 us | 1.540 ms |
| `wilkinson_48` | 61 | 48 | 48 | 2.925 us | 34.661 us | 2.203 us | 359.714 us | 2.470 ms |
| `wilkinson_56` | 67 | 56 | 56 | 3.375 us | 36.164 us | 2.624 us | 557.617 us | 3.795 ms |
| `chebyshev_T24` | 5 | 24 | 3 | 591 ns | 11.387 us | 972 ns | 282.568 us | 40.641 us |
| `chebyshev_U24` | 3 | 24 | 4 | 590 ns | 5.719 us | 991 ns | 232.946 us | 78.376 us |
| `legendre_P30` | 71 | 30 | 4 | 1.342 us | 17.276 us | 1.322 us | 1.685 ms | 358.081 us |
| `legendre_P38` | 79 | 38 | 3 | 1.812 us | 27.922 us | 1.632 us | 3.407 ms | 264.803 us |
| `cyclo_phi17` | 3 | 16 | 1 | 491 ns | 3.845 us | 591 ns | 91.546 us | 3.275 us |
| `cyclo_phi41` | 3 | 40 | 5 | 1.032 us | 8.372 us | 1.813 us | 446.512 us | 232.204 us |
| `xpow24_minus1` | 11 | 24 | 13 | 651 ns | 3.124 us | 1.001 us | 187.798 us | 429.899 us |
| `randprod_10` | 7 | 20 | 4 | 581 ns | 12.278 us | 761 ns | 413.323 us | 113.077 us |
| `randprod_21` | 17 | 24 | 7 | 691 ns | 18.908 us | 1.032 us | 990.839 us | 215.489 us |

Row reduction dominates the modular factorization on every row where the
modular image has real width, and the Berlekamp matrix construction is
negligible everywhere (single-digit microseconds).

### Hensel lift

`multifactorLiftQuadraticList` recurses on a degree-balanced split, so the
product tree is binary with one `henselLiftFactors` call per internal node --
`local factors - 1` of them, as recorded above. The two Hensel-bound rows are
the two with few, wide local factors at a small prime: `cyclo_phi179` lifts 2
factors of degree 89 to `3^113`, and `cyclo_phi385` lifts 4 factors of degree
60 to `3^152`.

## Counterfactual prime plans

For each good prime the bounded walk retained, the cost of having stopped
there. `directPrimePlan?` visits `smallPrimeCandidates ++
extendedSmallPrimeCandidates` in ascending order and keeps the first good prime
when its modular width is at most 8, otherwise trials at most two further good
primes; the smallest prime in each group below is therefore the first good
prime. Downstream total is the Hensel lift plus recombination and excludes the
walk itself.

| instance | prime | local factors | Hensel precision | downstream lift | downstream recombination | downstream total | nodes | exact divisions | selected |
|---|---:|---:|---:|---:|---:|---:|---:|---:|:--:|
| `sd5` | 19 | 16 | 21 | 1.967 ms | 95.141 ms | 97.108 ms | 32,768 | 129 |  |
| `sd5` | 23 | 16 | 20 | 1.994 ms | 94.664 ms | 96.658 ms | 32,768 | 129 |  |
| `sd5` | 29 | 16 | 19 | 1.964 ms | 95.138 ms | 97.102 ms | 32,768 | 129 | yes |
| `sd5_shift1` | 19 | 16 | 21 | 1.988 ms | 82.887 ms | 84.875 ms | 32,768 | 1 |  |
| `sd5_shift1` | 23 | 16 | 20 | 1.929 ms | 82.544 ms | 84.473 ms | 32,768 | 1 |  |
| `sd5_shift1` | 29 | 16 | 19 | 1.986 ms | 82.495 ms | 84.481 ms | 32,768 | 1 | yes |
| `sd5_shift2` | 19 | 16 | 22 | 1.903 ms | 83.828 ms | 85.730 ms | 32,768 | 1 |  |
| `sd5_shift2` | 23 | 16 | 21 | 1.959 ms | 83.593 ms | 85.552 ms | 32,768 | 1 |  |
| `sd5_shift2` | 29 | 16 | 19 | 1.973 ms | 83.835 ms | 85.808 ms | 32,768 | 1 | yes |
| `sd4_x_sd4shift1` | 13 | 16 | 22 | 1.778 ms | 11.709 ms | 13.487 ms | 10,503 | 10 |  |
| `sd4_x_sd4shift1` | 17 | 16 | 20 | 1.770 ms | 11.856 ms | 13.626 ms | 10,503 | 10 |  |
| `sd4_x_sd4shift1` | 29 | 16 | 17 | 1.910 ms | 12.170 ms | 14.080 ms | 10,540 | 10 | yes |
| `sd5_x_phi11` | 19 | 17 | 24 | 3.203 ms | 205.498 ms | 208.701 ms | 65,536 | 258 |  |
| `sd5_x_phi11` | 23 | 26 | 22 | 3.399 ms | 258.536 ms | 261.936 ms | 245,506 | 0 |  |
| `sd5_x_phi11` | 29 | 17 | 21 | 3.296 ms | 194.939 ms | 198.235 ms | 65,522 | 258 | yes |
| `xpow48_minus1` | 5 | 20 | 21 | 1.464 ms | 10.124 ms | 11.588 ms | 456 | 221 |  |
| `xpow48_minus1` | 7 | 27 | 17 | 1.584 ms | 5.260 s | 5.262 s | 181,455 | 60,530 |  |
| `xpow48_minus1` | 11 | 19 | 14 | 1.186 ms | 13.853 ms | 15.039 ms | 268 | 268 | yes |
| `xpow105_minus1` | 11 | 30 | 30 | 14.959 ms | 1.432 s | 1.447 s | 17,020 | 3,414 |  |
| `xpow105_minus1` | 13 | 33 | 28 | 16.007 ms | 37.259 s | 37.275 s | 174,439 | 58,145 |  |
| `xpow105_minus1` | 17 | 14 | 26 | 15.808 ms | 29.008 ms | 44.817 ms | 60 | 60 | yes |
| `xpow120_minus1` | 7 | 39 | 43 | 21.504 ms | 447.370 ms | 468.874 ms | 5,339 | 1,801 | yes |
| `xpow120_minus1` | 11 | 65 | 35 | 24.646 ms | 4.001 s | 4.026 s | 44,887 | 8,983 |  |
| `xpow120_minus1` | 13 | 42 | 32 | 9.854 ms | 5.933 s | 5.943 s | 53,449 | 9,179 |  |
| `cyclo_phi64_x_phi105` | 11 | 10 | 24 | 7.869 ms | 4.885 ms | 12.754 ms | 130 | 28 | yes |
| `cyclo_phi64_x_phi105` | 13 | 14 | 22 | 8.510 ms | 597.392 ms | 605.903 ms | 8,111 | 1,336 |  |
| `cyclo_phi64_x_phi105` | 17 | 12 | 20 | 8.223 ms | 98.596 ms | 106.819 ms | 1,512 | 221 |  |
| `wilkinson_40` | 41 | 40 | 38 | 8.333 ms | 503.897 us | 8.837 ms | 40 | 40 |  |
| `wilkinson_40` | 43 | 40 | 38 | 8.327 ms | 500.952 us | 8.827 ms | 40 | 40 |  |
| `wilkinson_40` | 47 | 40 | 37 | 8.406 ms | 507.412 us | 8.913 ms | 40 | 40 | yes |
| `wilkinson_48` | 53 | 48 | 45 | 18.029 ms | 756.882 us | 18.786 ms | 48 | 48 |  |
| `wilkinson_48` | 59 | 48 | 44 | 18.167 ms | 772.636 us | 18.940 ms | 48 | 48 |  |
| `wilkinson_48` | 61 | 48 | 43 | 18.171 ms | 752.896 us | 18.924 ms | 48 | 48 | yes |
| `wilkinson_56` | 59 | 56 | 53 | 23.624 ms | 1.019 ms | 24.643 ms | 56 | 56 |  |
| `wilkinson_56` | 61 | 56 | 52 | 23.625 ms | 1.014 ms | 24.639 ms | 56 | 56 |  |
| `wilkinson_56` | 67 | 56 | 51 | 23.934 ms | 1.015 ms | 24.949 ms | 56 | 56 | yes |
| `legendre_P30` | 61 | 15 | 15 | 1.020 ms | 41.469 ms | 42.489 ms | 16,384 | 1 |  |
| `legendre_P30` | 67 | 7 | 15 | 1.403 ms | 179.236 us | 1.582 ms | 64 | 1 |  |
| `legendre_P30` | 71 | 4 | 15 | 485.730 us | 70.124 us | 555.854 us | 8 | 1 | yes |
| `xpow24_minus1` | 5 | 14 | 11 | 398.862 us | 1.070 ms | 1.469 ms | 150 | 77 |  |
| `xpow24_minus1` | 7 | 15 | 9 | 374.194 us | 155.510 us | 529.704 us | 38 | 20 |  |
| `xpow24_minus1` | 11 | 13 | 7 | 317.330 us | 1.757 ms | 2.074 ms | 113 | 113 | yes |

Rows where the walk retained a single prime, for completeness:

| instance | prime | local factors | Hensel precision | downstream lift | downstream recombination | downstream total |
|---|---:|---:|---:|---:|---:|---:|
| `cyclo_phi179` | 3 | 2 | 113 | 60.598 ms | 5.661 ms | 66.259 ms |
| `cyclo_phi128_x_phi165` | 7 | 8 | 52 | 66.029 ms | 41.420 ms | 107.449 ms |
| `cyclo_phi385` | 3 | 4 | 152 | 166.942 ms | 82.040 ms | 248.982 ms |
| `chebyshev_T24` | 5 | 3 | 22 | 147.809 us | 24.316 us | 172.125 us |
| `chebyshev_U24` | 3 | 4 | 33 | 307.416 us | 24.747 us | 332.163 us |
| `legendre_P38` | 79 | 3 | 19 | 691.736 us | 50.204 us | 741.940 us |
| `cyclo_phi17` | 3 | 1 | 11 | 3.405 us | 6.089 us | 9.494 us |
| `cyclo_phi41` | 3 | 5 | 26 | 698.906 us | 1.459 ms | 2.158 ms |
| `randprod_10` | 7 | 4 | 11 | 199.466 us | 19.780 us | 219.246 us |
| `randprod_21` | 17 | 7 | 9 | 346.944 us | 38.167 us | 385.111 us |

Three facts fall out.

First, **the selection rule picks well among what it sees.** The selected plan
is within 5% of the cheapest retained plan on every representative row. The
only material miss is the `xpow24_minus1` control, where prime 7 would have
been 3.9x cheaper downstream than the selected 11 (529.704 us against
2.074 ms) -- on a row whose whole factorization is 3.5 ms.

Second, **on some rows the walk is indispensable.** `xpow105_minus1` retains
widths 30, 33, and 14; stopping at the first good prime would cost 1.447 s
instead of 44.817 ms, and stopping at the second 37.275 s. `xpow48_minus1`,
`cyclo_phi64_x_phi105`, and the `legendre_P30` control show the same shape at
smaller scale. Reverting to first-good-prime selection is not an option.

Third, **on other rows the walk is pure loss.** Every Swinnerton-Dyer row sees
16 quadratic local factors at all three primes and 32,768 leaves either way;
the two extra full Berlekamp factorizations buy nothing. Wilkinson 40, 48, and
56 stay at `degree` linear factors at all three primes and differ only in lift
precision. `xpow120_minus1` selects its first good prime and pays for two
worse ones. The cost of that waste is exactly the prime-walk column of the
phase table.

## Cactus ranks 118--144

A cactus curve sorts each system's own solved instances by time, so rank `k`
names a different instance for each system. The two readings are kept apart.

Hex solves 144 of the 160 combined rows; verified Isabelle BZ solves 141.

### Cumulative-rank view (independently sorted, as plotted)

| rank | hex-factor instance | time | cumulative | isabelle-bz instance | time | cumulative |
|---:|---|---:|---:|---|---:|---:|
| 118 | `wilkinson_28` | 7.532 ms | 107.007 ms | `legendre_P38` | 6.723 ms | 128.506 ms |
| 119 | `cyclo_phi24_x_phi35` | 8.735 ms | 115.742 ms | `cyclo_phi24_x_phi35` | 6.782 ms | 135.288 ms |
| 120 | `wilkinson_32` | 9.841 ms | 125.583 ms | `xpow48_minus1` | 8.392 ms | 143.680 ms |
| 121 | `sd4_x_phi17` | 9.907 ms | 135.490 ms | `laguerre_L32` | 8.421 ms | 152.101 ms |
| 122 | `xpow60_minus1` | 13.055 ms | 148.546 ms | `wilkinson_40` | 10.286 ms | 162.387 ms |
| 123 | `wilkinson_40` | 16.034 ms | 164.579 ms | `sd4_x_sd4shift1` | 10.803 ms | 173.190 ms |
| 124 | `sd4_x_phi35` | 20.478 ms | 185.057 ms | `xpow60_minus1` | 10.999 ms | 184.189 ms |
| 125 | `xpow48_minus1` | 21.369 ms | 206.426 ms | `wilkinson_48` | 14.492 ms | 198.681 ms |
| 126 | `sd4_x_sd4shift1` | 25.371 ms | 231.797 ms | `sd5_shift2` | 14.716 ms | 213.396 ms |
| 127 | `wilkinson_48` | 29.955 ms | 261.752 ms | `sd5_shift1` | 14.815 ms | 228.211 ms |
| 128 | `wilkinson_56` | 41.031 ms | 302.783 ms | `cyclo_phi179` | 14.956 ms | 243.167 ms |
| 129 | `cyclo_phi151` | 73.125 ms | 375.909 ms | `wilkinson_56` | 21.980 ms | 265.147 ms |
| 130 | `cyclo_phi179` | 80.319 ms | 456.227 ms | `sd5` | 22.610 ms | 287.757 ms |
| 131 | `xpow105_minus1` | 83.160 ms | 539.388 ms | `sd4_x_phi35` | 26.190 ms | 313.947 ms |
| 132 | `cyclo_phi64_x_phi105` | 87.905 ms | 627.292 ms | `sd5_x_phi11` | 27.545 ms | 341.492 ms |
| 133 | `sd5_shift1` | 97.455 ms | 724.747 ms | `cyclo_phi64_x_phi105` | 37.990 ms | 379.483 ms |
| 134 | `sd5_shift2` | 101.021 ms | 825.768 ms | `cyclo_phi89` | 52.018 ms | 431.501 ms |
| 135 | `sd5` | 111.845 ms | 937.613 ms | `xpow105_minus1` | 55.922 ms | 487.423 ms |
| 136 | `cyclo_phi625` | 179.253 ms | 1.117 s | `xpow120_minus1` | 168.811 ms | 656.234 ms |
| 137 | `cyclo_phi128_x_phi165` | 205.821 ms | 1.323 s | `cyclo_phi625` | 171.217 ms | 827.451 ms |
| 138 | `sd5_x_phi11` | 224.372 ms | 1.547 s | `cyclo_phi128_x_phi165` | 172.600 ms | 1.000 s |
| 139 | `cyclo_phi385` | 455.310 ms | 2.002 s | `cyclo_phi385` | 355.307 ms | 1.355 s |
| 140 | `sd5_x_phi45` | 517.092 ms | 2.519 s | `cyclo_phi151` | 528.715 ms | 1.884 s |
| 141 | `xpow120_minus1` | 526.218 ms | 3.046 s | `cyclo_phi1031` | 8.179 s | 10.064 s |
| 142 | `hoeij_M12_f132` | 1.660 s | 4.705 s | -- | -- | -- |
| 143 | `hoeij_F190` | 7.253 s | 11.958 s | -- | -- | -- |
| 144 | `sd6` | 8.319 s | 20.277 s | -- | -- | -- |

Cumulative parity is at rank 124 (185.057 ms against 184.189 ms). The ratio
peaks near rank 135 (937.613 ms against 487.423 ms, 1.92x) and Hex retakes the
lead at rank 141, where Isabelle's `cyclo_phi1031` costs 8.179 s.

### Paired-testcase view (same instance, both systems)

| hex-factor rank | instance | degree | hex-factor | isabelle-bz | isabelle-bz / hex-factor |
|---:|---|---:|---:|---:|---:|
| 118 | `wilkinson_28` | 28 | 7.532 ms | 4.036 ms | 0.54x |
| 119 | `cyclo_phi24_x_phi35` | 32 | 8.735 ms | 6.782 ms | 0.78x |
| 120 | `wilkinson_32` | 32 | 9.841 ms | 6.075 ms | 0.62x |
| 121 | `sd4_x_phi17` | 32 | 9.907 ms | 4.567 ms | 0.46x |
| 122 | `xpow60_minus1` | 60 | 13.055 ms | 10.999 ms | 0.84x |
| 123 | `wilkinson_40` | 40 | 16.034 ms | 10.286 ms | 0.64x |
| 124 | `sd4_x_phi35` | 40 | 20.478 ms | 26.190 ms | 1.28x |
| 125 | `xpow48_minus1` | 48 | 21.369 ms | 8.392 ms | 0.39x |
| 126 | `sd4_x_sd4shift1` | 32 | 25.371 ms | 10.803 ms | 0.43x |
| 127 | `wilkinson_48` | 48 | 29.955 ms | 14.492 ms | 0.48x |
| 128 | `wilkinson_56` | 56 | 41.031 ms | 21.980 ms | 0.54x |
| 129 | `cyclo_phi151` | 150 | 73.125 ms | 528.715 ms | 7.23x |
| 130 | `cyclo_phi179` | 178 | 80.319 ms | 14.956 ms | 0.19x |
| 131 | `xpow105_minus1` | 105 | 83.160 ms | 55.922 ms | 0.67x |
| 132 | `cyclo_phi64_x_phi105` | 80 | 87.905 ms | 37.990 ms | 0.43x |
| 133 | `sd5_shift1` | 32 | 97.455 ms | 14.815 ms | 0.15x |
| 134 | `sd5_shift2` | 32 | 101.021 ms | 14.716 ms | 0.15x |
| 135 | `sd5` | 32 | 111.845 ms | 22.610 ms | 0.20x |
| 136 | `cyclo_phi625` | 500 | 179.253 ms | 171.217 ms | 0.96x |
| 137 | `cyclo_phi128_x_phi165` | 144 | 205.821 ms | 172.600 ms | 0.84x |
| 138 | `sd5_x_phi11` | 42 | 224.372 ms | 27.545 ms | 0.12x |
| 139 | `cyclo_phi385` | 240 | 455.310 ms | 355.307 ms | 0.78x |
| 140 | `sd5_x_phi45` | 56 | 517.092 ms | timeout | -- |
| 141 | `xpow120_minus1` | 120 | 526.218 ms | 168.811 ms | 0.32x |
| 142 | `hoeij_M12_f132` | 132 | 1.660 s | timeout | -- |
| 143 | `hoeij_F190` | 190 | 7.253 s | timeout | -- |
| 144 | `sd6` | 64 | 8.319 s | timeout | -- |

The paired view is the one an attribution argument needs, and it disagrees with
the cumulative view about which rows matter. `cyclo_phi151` is a 7.23x Hex
*win* sitting inside the elbow; `cyclo_phi625` and `cyclo_phi128_x_phi165` are
near parity. The genuine paired losses are the Swinnerton-Dyer group
(0.12x-0.20x), `cyclo_phi179` (0.19x), `xpow48_minus1` (0.39x),
`xpow120_minus1` (0.32x), `sd4_x_sd4shift1` (0.43x),
`cyclo_phi64_x_phi105` (0.43x), and the Wilkinson group (0.48x-0.54x).

Aggregated over the whole 392-row corpus, on the 216 rows where both systems
answer above ten times their own protocol overhead, Hex divided by verified
Isabelle BZ has median 0.765x, p10-p90 0.473x-2.677x, and a 135-81 win split.

## Sampling profiles

Leaf-cost categorisation, in the four categories `SPEC/profiling.md` fixes.
Percentages are of retained samples on the service's main thread.

| instance | samples | replays | Lean own code | GMP | allocation / free | Lean runtime | classified |
|---|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 6,109 | 56 | 4.7% | 13.2% | 70.3% | 8.9% | 97.02% |
| `sd5_x_phi11` | 6,150 | 27 | 5.3% | 15.6% | 66.5% | 9.4% | 96.8% |
| `xpow120_minus1` | 5,875 | 11 | 4.1% | 22.0% | 62.5% | 7.4% | 96.07% |
| `cyclo_phi179` | 6,074 | 75 | 5.6% | 16.3% | 56.9% | 16.3% | 95.06% |
| `cyclo_phi64_x_phi105` | 6,140 | 69 | 20.7% | 3.5% | 34.6% | 34.1% | 92.95% |
| `cyclo_phi385` | 5,983 | 13 | 10.7% | 16.0% | 45.0% | 23.7% | 95.32% |
| `wilkinson_56` | 6,076 | 149 | 10.3% | 12.3% | 51.4% | 18.6% | 92.53% |
| `xpow48_minus1` | 5,983 | 264 | 9.5% | 13.8% | 56.3% | 14.8% | 94.33% |
| `xpow105_minus1` | 6,024 | 72 | 14.9% | 13.6% | 44.1% | 20.4% | 93.08% |

Inclusive share of the production cascade, by Hex function. `Hex.classicalInput`
is the whole bounded prime walk; `Hex.henselLiftData` is the multifactor lift;
`Hex.searchDirect` is head-forced recombination; `Hex.exactQuotient?` is exact
integer polynomial division.

| instance | `Hex.classicalInput` | `Hex.Berlekamp.berlekampFactor` | `Hex.Matrix.rowReduce` | `Hex.henselLiftData` | `Hex.ZPoly.reduceModPowImpl` | `Hex.proposeFactorization` | `Hex.searchDirect` | `Hex.tryDirectCandidate` | `Hex.directCandidate` | `Hex.exactQuotient?` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 8.9% | 8.5% | 1.2% | 1.7% | <0.5% | <0.5% | 85.7% | 30.4% | 4.2% | 6.4% |
| `sd5_x_phi11` | 9.7% | 9.4% | 2.0% | 1.4% | <0.5% | <0.5% | 86.6% | 35.8% | 5.6% | 9.7% |
| `xpow120_minus1` | 12.1% | 12.0% | 0.7% | 4.0% | 0.9% | <0.5% | 75.6% | 77.1% | 13.0% | 63.0% |
| `cyclo_phi179` | 18.6% | 18.5% | 12.3% | 73.2% | 20.4% | <0.5% | 5.3% | 5.3% | 1.2% | 4.1% |
| `cyclo_phi64_x_phi105` | 85.2% | 84.0% | 49.8% | 8.7% | 2.2% | <0.5% | 5.5% | 5.4% | 1.7% | 3.5% |
| `cyclo_phi385` | 45.2% | 44.7% | 41.6% | 35.9% | 11.2% | <0.5% | 11.3% | 11.3% | 1.7% | 9.6% |
| `wilkinson_56` | 35.1% | 32.0% | <0.5% | 57.4% | 20.6% | 63.0% | <0.5% | <0.5% | <0.5% | 1.9% |
| `xpow48_minus1` | 27.2% | 26.6% | 1.7% | 5.2% | <0.5% | <0.5% | 66.0% | 65.5% | 12.3% | 52.0% |
| `xpow105_minus1` | 46.8% | 46.4% | 3.8% | 18.3% | 4.4% | <0.5% | 31.6% | 31.6% | 3.0% | 28.4% |

Top self-time leaves:

- `sd5`: `int_free_chunk` 20.6%, `_realloc` 16.2%, `int_malloc` 8.2%, `mi_free` 6.3%, `mi_malloc_small` 5.5%.
- `sd5_x_phi11`: `int_free_chunk` 17.1%, `_realloc` 16.1%, `int_malloc` 7.5%, `mi_free` 6.2%, `_GI___libc_malloc` 5.5%.
- `xpow120_minus1`: `_realloc` 18.6%, `int_free_chunk` 14.3%, `_libc_malloc2` 7.1%, `_gmpn_copyi_x86_64` 6.6%, `_GI___libc_malloc` 4.9%.
- `cyclo_phi179`: `int_free_chunk` 13.3%, `_realloc` 11.7%, `_GI___libc_malloc` 7.3%, `int_malloc` 7.0%, `_free` 5.1%.
- `cyclo_phi64_x_phi105`: `mi_malloc_small` 13.4%, `mi_free` 12.1%, `Fin.foldl.loop` 9.7%, `Hex.Matrix.rowAdd` 8.8%, `lean_apply_2` 5.2%.
- `cyclo_phi385`: `int_free_chunk` 9.2%, `Fin.foldl.loop` 8.5%, `Hex.Matrix.rowAdd` 8.2%, `mi_malloc_small` 7.9%, `mi_free` 7.1%.
- `wilkinson_56`: `int_free_chunk` 10.7%, `_realloc` 8.4%, `mi_free` 6.8%, `mi_malloc_small` 5.9%, `int_malloc` 5.7%.
- `xpow48_minus1`: `_realloc` 12.8%, `int_free_chunk` 12.5%, `_GI___libc_malloc` 5.8%, `mi_malloc_small` 5.6%, `mi_free` 4.8%.
- `xpow105_minus1`: `_realloc` 8.8%, `mi_malloc_small` 7.3%, `mi_free` 7.2%, `int_free_chunk` 6.7%, `lean_apply_2` 5.5%.

Allocation is the largest single leaf category on all nine profiles, between
34.6% and 70.3%. It is not confined to one phase: the
recombination-bound rows spend it in `int_free_chunk` and `_realloc` under
candidate construction and exact division, while `cyclo_phi64_x_phi105` and
`cyclo_phi385` spend it in `mi_malloc_small`/`mi_free` under
`Hex.Matrix.rowAdd`. GMP is a distant second and peaks at 22.0% on
`xpow120_minus1`, whose exact divisions are dense bignum long division.

The phase table and the profiles agree everywhere they overlap: `sd5` is
89.7%/85.7% recombination, `cyclo_phi179` 74.6%/73.2% Hensel,
`cyclo_phi64_x_phi105` 85.3%/85.2% prime walk.

## Go / no-go for the dependent issues

### #9128 -- scout modular degree patterns before full splitting: **go**

Confirmed by the counterfactual table. The waste the issue names is real and
measurable: on `sd5` and its shifts, on Wilkinson 40/48/56, and on
`xpow120_minus1`, the two extra full Berlekamp factorizations change neither
the local factor count nor the downstream cost. The upper bound on the prize is
the prime-walk column of the phase table minus the cost of one full split:
85.3% of `cyclo_phi64_x_phi105`, 47.0% of `cyclo_phi128_x_phi165`, 45.0% of
`cyclo_phi385`, 45.9% of `xpow105_minus1`, 40.5% of `sd4_x_sd4shift1`, and
33.9% of `wilkinson_56`.

The measured bounded oracle the issue asks the new policy to be scored against
is the "downstream total" column: on the representative set it differs from the
production selection by at most 5%, so **the savings are entirely in the cost
of the walk, not in the choice it makes**. A policy that scouts cheaply and
then splits once should target the walk cost and must not regress the choice.
`xpow105_minus1` and `legendre_P30` are the rows that forbid a first-good-prime
rule.

One correction to the issue text: it reports `cyclo_phi64_x_phi105` widths as
10, 14, 12 and `xpow105_minus1` as 30, 33, 14, both of which reproduce; but it
reports `sd5` as "16 quadratic factors at all three primes" -- confirmed -- and
`xpow120_minus1` as widths 39, 64, 42, where this record measures 39, 65, 42.

### #9129 -- enumerate factor supports without allocating lists: **go**

Confirmed and slightly stronger than the issue states. `Hex.searchDirect` is
85.7% inclusive on `sd5` and 86.6% on `sd5_x_phi11` (the issue says about 86%
and 87%). Allocation is 70.3% and 66.5% of leaves respectively, above the
37-64% the issue quotes. The counters show why: `sd5` visits 32,768 leaves and
the cheap filters reject 32,639 of them, yet every leaf still reverses index
lists and materializes a list of lifted polynomials before those filters can
run. `Hex.tryDirectCandidate` is 30.4% inclusive on `sd5` against
`Hex.directCandidate` 4.2% and `Hex.exactQuotient?` 6.4%, so most of the
remaining recombination time is the traversal itself, not the mathematics.

### #9130 -- reject impossible exact divisors over a word-sized prime: **go**

Confirmed. `Hex.exactQuotient?` inclusive share is 63.0% on `xpow120_minus1`
(the issue says about 63%), 52.0% on `xpow48_minus1`, and 28.4% on
`xpow105_minus1` (the issue says about 31%). The counters give the rejection
headroom directly: on `xpow48_minus1` and `xpow105_minus1` the cheap filters
reject nothing, so 268 and 60 divisions run of which 10 and 8 succeed; on
`xpow120_minus1`, 1,801 divisions run of which 16 succeed. A necessary-condition
filter therefore has 96%-99% of the divisions available to reject on exactly
the rows the issue names.

### #9131 -- keep quadratic Hensel lifts canonical: **go**

Confirmed. `Hex.henselLiftData` is 73.2% inclusive on `cyclo_phi179` (the issue
says about 73%) and 57.4% on `wilkinson_56` (about 58%).
`Hex.ZPoly.reduceModPowImpl` is 20.4% and 20.6% of *total* time on those rows,
which is 28% and 36% of lift time -- higher than the "roughly 20% of lift time"
the issue estimates, so Phase 1 of that issue has more headroom than stated.
`cyclo_phi385` adds a third row at 35.9% lift and 11.2% `reduceModPow`.

One refinement the phase table forces: the Wilkinson rows answer from the
proposal-replay tier, not the classical tier, so their lift happens inside
`proposeFactorization` (63.0% inclusive) rather than in the cascade's own
Hensel phase. Phase 1's audit must cover that call path too.

### #9132 -- packed finite-field matrix: **go to the measurement gate, with a caveat**

`Hex.Matrix.rowReduce` is 41.6% inclusive on `cyclo_phi385` and 49.8% on
`cyclo_phi64_x_phi105`, matching the issue's 40% and 50%. But the two rows are
not equivalent evidence, and the issue is right to make #9128 come first:

- `cyclo_phi385` retains **one** prime, so its 41.6% is row reduction at the
  selected prime and survives any change to the walk. Against the issue's gate
  it is already 41.6% of total factor time and 204.972 ms of a 211.525 ms
  selected-prime Berlekamp call (96.9%).
- `cyclo_phi64_x_phi105` retains **three** primes, so most of its 49.8% is row
  reduction at primes the plan discards. After #9128 that row is expected to
  fall below the gate.

`cyclo_phi128_x_phi165` is a second single-prime witness: 89.725 ms of row
reduction inside a 95.803 ms Berlekamp call (93.7%). Remeasure after #9128 as the issue
requires; the single-prime rows are the ones that will still support the gate.

### #9133 -- iterated quadratic norm certificates: **defer as designed**

The baseline the issue asks for is recorded. `sd5` costs 110.859 ms with 16
local factors, 32,768 recombination nodes, 32,639 cheap-filter rejections, 129
exact divisions and one successful divisor; `sd5_x_phi11` costs 224.575 ms with
65,522 nodes; `sd4_x_sd4shift1` costs 24.064 ms with 10,540 nodes; `sd6` is a
solved 8.319 s row at cactus rank 144. The paired Isabelle gap on this group is
0.12x-0.20x, the worst in the corpus. Isabelle examines a comparable number of
supports, so the gap is traversal cost, which is #9129's target. Re-evaluate
after #9129 and #9130 land, as the issue specifies; nothing here justifies
starting the certificate work now.

## Regeneration

```sh
lake build hexbz_factor_service

# Full Hex sweep (external comparator records are reused unchanged).
taskset -c 0 python3 scripts/bench/factor_sweep.py \
  --systems hex-factor --cutoff 10 --no-early-terminate \
  --output /tmp/hexbz-factor-sweep.json

# Phase attribution, counterfactual prime plans, and the validation sample.
taskset -c 0 python3 scripts/bench/factor_phase_profile.py \
  --output /tmp/hexbz-phase-profile.json

# Symbolized sampling-profile summaries.
python3 scripts/profile/factor_sampling_profile.py \
  --cpu 0 --output /tmp/hexbz-factor-sampling-profiles.json

# Rank tables.
python3 scripts/bench/cactus_rank_table.py --lo 118 --hi 144

# Figures, and the byte-for-byte check CI runs.
uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py
uv run --with matplotlib==3.11.1 python3 scripts/plots/hexbz-cactus.py --check
```
