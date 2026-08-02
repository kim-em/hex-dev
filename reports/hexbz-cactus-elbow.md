# HexBZ Cactus Elbow: Phase-Attributed Baseline

> The prime-planning policy this report baselines was replaced by issue #9128:
> the walk now scouts modular degree patterns and splits at most two candidate
> primes. See [hexbz-prime-scout.md](hexbz-prime-scout.md). Everything below is
> the record as measured at revision `c34ffbbb`.

The combined cross-system cactus has Hex ahead of the verified Isabelle
Berlekamp-Zassenhaus extraction through solved rank 124, behind it from 125
through 140, and ahead again from 141 once Isabelle meets `cyclo_phi1031`.
This page is the durable attribution record for that elbow: where the time
goes, phase by phase, on the rows that populate it, and what a different
modular prime would have cost.

Every number here is reproducible from committed records by the commands in
[Regeneration](#regeneration).

**This page is the snapshot at revision `c34ffbbb`, and stays that way.** The
recombination traversal it attributes has since changed: see
[hexbz-support-traversal.md](hexbz-support-traversal.md), which supersedes the
`sd5` and `sd5_x_phi11` rows of the tables below and carries the current
cactus record. The go/no-go verdicts for the dependent issues were reached
against the numbers here and are not restated there.

## Revision and protocol

- Source revision `c34ffbbbc16bd8c93274d96f555e22e1bb8868bc` (clean worktree),
  Lean toolchain `leanprover/lean4:v4.33.0-rc1`.
- Host `chungus2`, AMD EPYC 9455, Linux x86-64, 96 cores.
- The measurement harness and the measured service were pinned to CPU 0 with
  `taskset -c 0`; the sampling profiles pinned the service to CPU 0 the same
  way. Nothing else ran on the host during a measurement.
- Corpus `bench/corpus/hexbz-factor-corpus.jsonl`, 392 rows, SHA-256
  `619913904240834c912489e6cc23ba136e8cc5ebf0ea95f83397e0682387284d`. The
  combined mix-doctrine mixture the cactus plots is its 160 `combined` rows.
- `hexbz_factor_service` SHA-256
  `8835c9e760e8b671c51b6311f7da718e7edefeea8d3924125a9b76cf8357dc79`.
- Cross-system sweep: persistent warm services, ten-second per-call cutoff,
  median of five calls below one second and one call otherwise, early
  termination disabled. Measured protocol overhead 21.732 us per Hex call;
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
| `reports/bench-results/hexbz-factor-sweep-c34ffbbb-hex-chungus2.json` | `821f3d2dd9753b5d4e69a15501c42d6f833609c95e088d5f5f409b5e3a108572` |
| `reports/bench-results/hexbz-factor-sweep-aa68c920-chungus2.json` | `4de27e389d738abc1e878f0be273485c3723216211a101c3eba55860e7b8a242` |
| `reports/bench-results/hexbz-phase-profile-c34ffbbb-chungus2.json` | `372e9882ef3d8bec2725e150d4490556f0867be02b4cf49bf293ddc3ef43aa26` |
| `reports/bench-results/hexbz-factor-sampling-profiles-c34ffbbb-chungus2.json` | `e0ef7e22181628a77262da3ec06d5acc1ef3370cdd87414de274096c54482f89` |

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
`directLiftedBasis`, direct recombination, factor validation, assembly with the
self-certifying product check, and whichever of the proposal-replay,
CLD-lattice, and trial-division tiers answers. Assembly and certification run
exactly once, and the fall-through to the trial backstop follows the production
policy: constant, quadratic, classical, and lattice answers are self-certified,
while proposal replay and trial division are accepted unconditionally, as
`runFactor` accepts them. Times, small-allocation counts (Lean's per-thread
heartbeat counter is the number of small allocations), and every structural
counter come from that one execution.

Recombination is the one place the diagnostic does not call the production
function verbatim. The production head-forced search records only a leaf count,
so `countedSearch` mirrors `searchDirect` leaf for leaf -- same traversal
order, same budget rule, and the same shared leaf predicates
(`directDegreePrefilter`, `directTrailingPrefilter`, `directCandidate`,
`shouldRecordPolynomialFactor`, `exactQuotient?`) -- while threading the
`DirectCandidateStats` stage counters that the unforced sweep already records.
The mirror also materializes the selected lifted factors where
`scanDirectCombinations` materializes them, as the argument written before
`tryDirectCandidate` evaluates its filters, rather than sinking that list into
the surviving branch; on `sd5` that is the path 32,639 of 32,768 leaves take,
and it is exactly the allocation the recombination phase is meant to measure.

The modular sub-phase breakdown is deliberately *not* part of the timed
cascade. It repeats the modular factorization at the already-selected prime
after the cascade's total mark, so it cannot perturb the cache, allocator, or
memory state of the phases it describes.

### Validation

Four checks ran on a wider sample than the representative set, over the 367
corpus rows the direct classical tier answers inside a two-second cutoff. The
counted mirror agrees with the production `factorTrace` on

- leaf count: **367 of 367**;
- selected prime: **367 of 367**;
- completed subset cardinalities: **367 of 367**;
- returned factor-degree multiset: **367 of 367**.

The phase-decomposed total tracks the untimed end-to-end `factor` call with
median ratio **0.989** and maximum **1.013**, so the decomposition and the
extra stage counters cost at most about 1.3% of the cascade. All five are
recomputed on every run and the driver exits non-zero on any disagreement.

## Phase attribution

Shares are of that execution's own total. `wilkinson_*` answers from the
proposal-replay tier, so its Hensel lift and recombination happen inside
`proposeFactorization` and show up in the last column; the sampling profiles
below separate them.

| instance | degree | method | total | normalize | prime walk | Hensel lift | recombination | proposal / lattice / trial | small allocations |
|---|---:|---|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 32 | classical | 103.698 ms | 0.0% | 9.1% | 1.9% | 88.9% | 0.0% | 4,152,714 |
| `sd5_shift1` | 32 | classical | 92.615 ms | 0.1% | 11.3% | 2.1% | 86.4% | 0.0% | 4,059,260 |
| `sd5_shift2` | 32 | classical | 96.691 ms | 0.1% | 13.1% | 2.1% | 84.7% | 0.0% | 4,279,431 |
| `sd4_x_sd4shift1` | 32 | classical | 23.575 ms | 0.2% | 41.2% | 8.1% | 50.1% | 0.0% | 1,482,215 |
| `sd5_x_phi11` | 42 | classical | 213.179 ms | 0.0% | 10.2% | 1.4% | 88.3% | 0.0% | 9,143,765 |
| `xpow48_minus1` | 48 | classical | 20.911 ms | 0.1% | 29.3% | 5.6% | 64.8% | 0.0% | 824,757 |
| `xpow105_minus1` | 105 | classical | 82.241 ms | 0.0% | 46.8% | 18.6% | 34.3% | 0.0% | 4,034,081 |
| `xpow120_minus1` | 120 | classical | 523.412 ms | 0.0% | 12.3% | 4.0% | 83.6% | 0.0% | 11,264,478 |
| `cyclo_phi179` | 178 | classical | 79.754 ms | 0.1% | 18.5% | 74.4% | 6.9% | 0.0% | 2,735,473 |
| `cyclo_phi64_x_phi105` | 80 | classical | 87.069 ms | 0.2% | 85.1% | 9.0% | 5.6% | 0.0% | 7,120,172 |
| `cyclo_phi128_x_phi165` | 144 | classical | 204.536 ms | 0.3% | 47.5% | 31.8% | 20.3% | 0.0% | 10,911,052 |
| `cyclo_phi385` | 240 | classical | 452.870 ms | 0.3% | 45.2% | 36.5% | 18.1% | 0.0% | 22,964,874 |
| `wilkinson_40` | 40 | replay | 15.639 ms | 0.5% | 38.0% | 0.0% | 0.0% | 59.8% | 752,683 |
| `wilkinson_48` | 48 | replay | 29.666 ms | 0.3% | 32.1% | 0.0% | 0.0% | 66.2% | 1,257,627 |
| `wilkinson_56` | 56 | replay | 40.331 ms | 0.3% | 34.4% | 0.0% | 0.0% | 63.9% | 1,787,621 |
| `chebyshev_T24` (control) | 24 | classical | 527.873 us | 3.3% | 65.3% | 24.3% | 4.2% | 0.0% | 39,412 |
| `chebyshev_U24` (control) | 24 | classical | 673.769 us | 2.7% | 48.4% | 41.9% | 3.9% | 0.0% | 44,195 |
| `legendre_P30` (control) | 30 | classical | 8.247 ms | 0.4% | 92.5% | 5.7% | 0.9% | 0.0% | 707,241 |
| `legendre_P38` (control) | 38 | classical | 4.655 ms | 0.9% | 82.9% | 14.1% | 1.1% | 0.0% | 388,609 |
| `cyclo_phi17` (control) | 16 | classical | 126.228 us | 6.0% | 81.5% | 1.7% | 4.0% | 0.0% | 9,413 |
| `cyclo_phi41` (control) | 40 | classical | 2.857 ms | 0.6% | 24.7% | 24.5% | 49.5% | 0.0% | 122,825 |
| `xpow24_minus1` (control) | 24 | classical | 3.507 ms | 0.3% | 41.6% | 8.9% | 48.4% | 0.0% | 178,722 |
| `randprod_10` (control) | 20 | classical | 775.370 us | 2.7% | 71.0% | 21.6% | 2.7% | 0.0% | 58,749 |
| `randprod_21` (control) | 24 | classical | 1.719 ms | 1.6% | 75.0% | 19.8% | 2.4% | 0.0% | 133,965 |

### Where each representative row sits on the cactus

The sweep and the phase profile use different protocols -- the sweep is a
median of five warm calls including protocol overhead, the profile is one
decomposed execution -- so their totals differ by a few percent. The cactus
rank below is the sweep's.

| instance | total factor time | cactus rank | cumulative at that rank | Isabelle BZ on the same row |
|---|---:|---:|---:|---:|
| `sd5` | 106.911 ms | 135 | 931.644 ms | 22.610 ms |
| `sd5_shift1` | 96.670 ms | 133 | 725.020 ms | 14.815 ms |
| `sd5_shift2` | 99.713 ms | 134 | 824.733 ms | 14.716 ms |
| `sd4_x_sd4shift1` | 25.091 ms | 126 | 232.141 ms | 10.803 ms |
| `sd5_x_phi11` | 222.540 ms | 138 | 1.544 s | 27.545 ms |
| `xpow48_minus1` | 21.635 ms | 125 | 207.050 ms | 8.392 ms |
| `xpow105_minus1` | 84.464 ms | 131 | 539.890 ms | 55.922 ms |
| `xpow120_minus1` | 523.812 ms | 141 | 3.039 s | 168.811 ms |
| `cyclo_phi179` | 80.025 ms | 130 | 455.426 ms | 14.956 ms |
| `cyclo_phi64_x_phi105` | 88.460 ms | 132 | 628.350 ms | 37.990 ms |
| `cyclo_phi128_x_phi165` | 205.261 ms | 137 | 1.322 s | 172.600 ms |
| `cyclo_phi385` | 455.841 ms | 139 | 2.000 s | 355.307 ms |
| `wilkinson_40` | 15.912 ms | 123 | 164.650 ms | 10.286 ms |
| `wilkinson_48` | 29.732 ms | 127 | 261.873 ms | 14.492 ms |
| `wilkinson_56` | 40.396 ms | 128 | 302.269 ms | 21.980 ms |

Every representative row lands between ranks 123 and 141, which is the elbow.

The elbow rows split into three shapes. Swinnerton-Dyer rows and `x^n - 1` are
recombination-bound. `cyclo_phi179` is Hensel-bound. `cyclo_phi64_x_phi105`,
`cyclo_phi128_x_phi165`, `cyclo_phi385`, and every cheap control are prime-walk
bound -- though as the next section shows, only some of that walk cost is
avoidable.

### Recombination counters

| instance | local factors | Hensel precision | internal lifts | nodes | cheap-filter rejections | products materialized | exact divisions | successful divisors | rejectable divisions |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 16 | 19 | 15 | 32,768 | 32,639 | 129 | 129 | 1 | 99.2% |
| `sd5_shift1` | 16 | 19 | 15 | 32,768 | 32,767 | 1 | 1 | 1 | 0.0% |
| `sd5_shift2` | 16 | 19 | 15 | 32,768 | 32,767 | 1 | 1 | 1 | 0.0% |
| `sd4_x_sd4shift1` | 16 | 17 | 15 | 10,540 | 10,530 | 10 | 10 | 2 | 80.0% |
| `sd5_x_phi11` | 17 | 21 | 16 | 65,522 | 65,264 | 258 | 258 | 2 | 99.2% |
| `xpow48_minus1` | 19 | 14 | 18 | 268 | 0 | 268 | 268 | 10 | 96.3% |
| `xpow105_minus1` | 14 | 26 | 13 | 60 | 0 | 60 | 60 | 8 | 86.7% |
| `xpow120_minus1` | 39 | 43 | 38 | 5,339 | 3,538 | 1,801 | 1,801 | 16 | 99.1% |
| `cyclo_phi179` | 2 | 113 | 1 | 2 | 0 | 2 | 2 | 1 | 50.0% |
| `cyclo_phi64_x_phi105` | 10 | 24 | 9 | 130 | 102 | 28 | 28 | 2 | 92.9% |
| `cyclo_phi128_x_phi165` | 8 | 52 | 7 | 54 | 29 | 25 | 25 | 2 | 92.0% |
| `cyclo_phi385` | 4 | 152 | 3 | 8 | 0 | 8 | 8 | 1 | 87.5% |
| `wilkinson_40` | 40 | proposal tier | -- | -- | -- | -- | -- | -- | -- |
| `wilkinson_48` | 48 | proposal tier | -- | -- | -- | -- | -- | -- | -- |
| `wilkinson_56` | 56 | proposal tier | -- | -- | -- | -- | -- | -- | -- |
| `chebyshev_T24` | 3 | 22 | 2 | 3 | 1 | 2 | 2 | 2 | 0.0% |
| `chebyshev_U24` | 4 | 33 | 3 | 4 | 0 | 4 | 4 | 4 | 0.0% |
| `legendre_P30` | 4 | 15 | 3 | 8 | 7 | 1 | 1 | 1 | 0.0% |
| `legendre_P38` | 3 | 19 | 2 | 4 | 3 | 1 | 1 | 1 | 0.0% |
| `cyclo_phi17` | 1 | 11 | 0 | 1 | 0 | 1 | 1 | 1 | 0.0% |
| `cyclo_phi41` | 5 | 26 | 4 | 16 | 0 | 16 | 16 | 1 | 93.8% |
| `xpow24_minus1` | 13 | 7 | 12 | 113 | 0 | 113 | 113 | 8 | 92.9% |
| `randprod_10` | 4 | 11 | 3 | 5 | 3 | 2 | 2 | 2 | 0.0% |
| `randprod_21` | 7 | 9 | 6 | 13 | 10 | 3 | 3 | 3 | 0.0% |

The Swinnerton-Dyer rows exhaust every head-forced cardinality: 32,768 leaves
for 16 local factors, of which the cheap degree and trailing-coefficient
filters reject all but 129 (`sd5`) or 1 (its shifts). The `x^n - 1` rows are
the opposite: `xpow48_minus1`, `xpow105_minus1`, and `xpow24_minus1` reject
nothing cheaply, so every leaf becomes a materialized product and an attempted
exact division.

## What the prime walk costs, and what of that is avoidable

The prime-walk phase is not one thing. It contains the modular images and
good-prime tests of every rejected candidate, one full Berlekamp factorization
at the prime the plan finally selects -- which no policy can avoid -- and, when
the first good prime is too wide, up to two further full factorizations at
primes the plan discards. Only the last is what #9128 could remove. The table
below subtracts one selected-prime Berlekamp call (measured by the modular
repeat) from the walk to bound it, and reports selection quality separately.

| instance | total | prime walk | retained good primes | one selected-prime split | avoidable extra splitting | selected / cheapest retained plan |
|---|---:|---:|---:|---:|---:|---:|
| `sd5` | 103.698 ms | 9.460 ms (9.1%) | 3 | 3.533 ms | 5.928 ms (5.7%) | 1.004x |
| `sd5_shift1` | 92.615 ms | 10.503 ms (11.3%) | 3 | 3.669 ms | 6.834 ms (7.4%) | 1.000x |
| `sd5_shift2` | 96.691 ms | 12.704 ms (13.1%) | 3 | 5.150 ms | 7.554 ms (7.8%) | 1.000x |
| `sd4_x_sd4shift1` | 23.575 ms | 9.721 ms (41.2%) | 3 | 4.548 ms | 5.173 ms (21.9%) | 1.050x |
| `sd5_x_phi11` | 213.179 ms | 21.751 ms (10.2%) | 3 | 8.982 ms | 12.768 ms (6.0%) | 1.000x |
| `xpow48_minus1` | 20.911 ms | 6.123 ms (29.3%) | 3 | 2.089 ms | 4.033 ms (19.3%) | 1.308x |
| `xpow105_minus1` | 82.241 ms | 38.517 ms (46.8%) | 3 | 9.934 ms | 28.583 ms (34.8%) | 1.000x |
| `xpow120_minus1` | 523.412 ms | 64.448 ms (12.3%) | 3 | 16.786 ms | 47.663 ms (9.1%) | 1.000x |
| `cyclo_phi179` | 79.754 ms | 14.761 ms (18.5%) | 1 | 14.847 ms | 0 ns (0.0%) | -- |
| `cyclo_phi64_x_phi105` | 87.069 ms | 74.107 ms (85.1%) | 3 | 21.453 ms | 52.654 ms (60.5%) | 1.000x |
| `cyclo_phi128_x_phi165` | 204.536 ms | 97.186 ms (47.5%) | 1 | 95.448 ms | 1.739 ms (0.9%) | -- |
| `cyclo_phi385` | 452.870 ms | 204.678 ms (45.2%) | 1 | 206.418 ms | 0 ns (0.0%) | -- |
| `wilkinson_40` | 15.639 ms | 5.950 ms (38.0%) | 3 | 1.812 ms | 4.138 ms (26.5%) | 1.012x |
| `wilkinson_48` | 29.666 ms | 9.527 ms (32.1%) | 3 | 2.870 ms | 6.657 ms (22.4%) | 1.008x |
| `wilkinson_56` | 40.331 ms | 13.886 ms (34.4%) | 3 | 4.346 ms | 9.541 ms (23.7%) | 1.018x |

Three facts fall out, and they are separate claims.

**The walk is expensive, but three of the fifteen representative rows have
nothing to save.**
`cyclo_phi179`, `cyclo_phi128_x_phi165`, and `cyclo_phi385` retain a single
good prime: their 18.5%, 47.5%, and 45.2% prime-walk shares are one necessary
full factorization, and the avoidable remainder is 0.0%, 0.9%, and 0.0%. Those
rows are not #9128 prizes, whatever their prime-walk column says. The rows with
real headroom are `cyclo_phi64_x_phi105` (60.5% of total), `xpow105_minus1`
(34.8%), `wilkinson_40`/`48`/`56` (26.5%, 22.4%, 23.7%),
`sd4_x_sd4shift1` (21.9%), and `xpow48_minus1` (19.3%).

**The selection rule usually picks well among what it sees, with one material
miss.** The selected plan is within 5% of the cheapest retained plan on 11 of
the 12 representative rows that retain more than one prime. The exception is
`xpow48_minus1` at 1.308x: the selected prime 11 needs 15.021 ms downstream
where the retained prime 5 needs 11.482 ms. The `xpow24_minus1` control is
worse at 3.930x (2.100 ms against 534.423 us at prime 7), on a row whose whole
factorization is 3.5 ms.

**On some rows the walk is indispensable.** `xpow105_minus1` retains widths 30,
33, and 14; stopping at the first good prime would cost 1.438 s instead of
44.299 ms, and stopping at the second 36.732 s. `xpow120_minus1` retains widths
39, 65, and 42 and selects its first good prime, but the two it rejects would
have cost 3.966 s and 5.863 s, so the scouting is what protects it.
`xpow48_minus1`, `cyclo_phi64_x_phi105`, and the `legendre_P30` control show
the same shape. Reverting to first-good-prime selection is not an option.

Where the walk *is* pure loss is the rows whose extra splits change nothing:
every Swinnerton-Dyer row sees 16 quadratic local factors at all three primes
and 32,768 leaves either way, and Wilkinson 40, 48, and 56 stay at `degree`
linear factors at all three primes, differing only in lift precision.

### Counterfactual prime plans

For each good prime the bounded walk retained, the cost of having stopped
there. `directPrimePlan?` visits `smallPrimeCandidates ++
extendedSmallPrimeCandidates` in ascending order and keeps the first good prime
when its modular width is at most 8, otherwise trials at most two further good
primes; the smallest prime in each group below is therefore the first good
prime. Downstream total is the Hensel lift plus recombination and excludes the
walk itself.

| instance | prime | local factors | Hensel precision | downstream lift | downstream recombination | downstream total | nodes | exact divisions | selected |
|---|---:|---:|---:|---:|---:|---:|---:|---:|:--:|
| `sd5` | 19 | 16 | 21 | 1.990 ms | 91.997 ms | 93.988 ms | 32,768 | 129 |  |
| `sd5` | 23 | 16 | 20 | 1.951 ms | 91.914 ms | 93.865 ms | 32,768 | 129 |  |
| `sd5` | 29 | 16 | 19 | 1.953 ms | 92.266 ms | 94.219 ms | 32,768 | 129 | yes |
| `sd5_shift1` | 19 | 16 | 21 | 1.954 ms | 80.506 ms | 82.461 ms | 32,768 | 1 |  |
| `sd5_shift1` | 23 | 16 | 20 | 1.923 ms | 80.570 ms | 82.493 ms | 32,768 | 1 |  |
| `sd5_shift1` | 29 | 16 | 19 | 1.975 ms | 80.363 ms | 82.338 ms | 32,768 | 1 | yes |
| `sd5_shift2` | 19 | 16 | 22 | 1.887 ms | 82.480 ms | 84.367 ms | 32,768 | 1 |  |
| `sd5_shift2` | 23 | 16 | 21 | 1.965 ms | 82.076 ms | 84.041 ms | 32,768 | 1 |  |
| `sd5_shift2` | 29 | 16 | 19 | 1.964 ms | 81.857 ms | 83.821 ms | 32,768 | 1 | yes |
| `sd4_x_sd4shift1` | 13 | 16 | 22 | 1.734 ms | 11.389 ms | 13.122 ms | 10,503 | 10 |  |
| `sd4_x_sd4shift1` | 17 | 16 | 20 | 1.759 ms | 11.588 ms | 13.347 ms | 10,503 | 10 |  |
| `sd4_x_sd4shift1` | 29 | 16 | 17 | 1.879 ms | 11.893 ms | 13.772 ms | 10,540 | 10 | yes |
| `sd5_x_phi11` | 19 | 17 | 24 | 3.212 ms | 202.700 ms | 205.912 ms | 65,536 | 258 |  |
| `sd5_x_phi11` | 23 | 26 | 22 | 3.399 ms | 249.575 ms | 252.974 ms | 245,506 | 0 |  |
| `sd5_x_phi11` | 29 | 17 | 21 | 3.078 ms | 191.486 ms | 194.564 ms | 65,522 | 258 | yes |
| `xpow48_minus1` | 5 | 20 | 21 | 1.520 ms | 9.962 ms | 11.482 ms | 456 | 221 |  |
| `xpow48_minus1` | 7 | 27 | 17 | 1.591 ms | 5.181 s | 5.182 s | 181,455 | 60,530 |  |
| `xpow48_minus1` | 11 | 19 | 14 | 1.190 ms | 13.831 ms | 15.021 ms | 268 | 268 | yes |
| `xpow105_minus1` | 11 | 30 | 30 | 14.738 ms | 1.423 s | 1.438 s | 17,020 | 3,414 |  |
| `xpow105_minus1` | 13 | 33 | 28 | 15.906 ms | 36.716 s | 36.732 s | 174,439 | 58,145 |  |
| `xpow105_minus1` | 17 | 14 | 26 | 15.552 ms | 28.746 ms | 44.299 ms | 60 | 60 | yes |
| `xpow120_minus1` | 7 | 39 | 43 | 21.087 ms | 442.166 ms | 463.253 ms | 5,339 | 1,801 | yes |
| `xpow120_minus1` | 11 | 65 | 35 | 24.807 ms | 3.941 s | 3.966 s | 44,887 | 8,983 |  |
| `xpow120_minus1` | 13 | 42 | 32 | 9.751 ms | 5.854 s | 5.863 s | 53,449 | 9,179 |  |
| `cyclo_phi64_x_phi105` | 11 | 10 | 24 | 7.803 ms | 4.832 ms | 12.635 ms | 130 | 28 | yes |
| `cyclo_phi64_x_phi105` | 13 | 14 | 22 | 8.442 ms | 590.295 ms | 598.737 ms | 8,111 | 1,336 |  |
| `cyclo_phi64_x_phi105` | 17 | 12 | 20 | 8.360 ms | 97.699 ms | 106.060 ms | 1,512 | 221 |  |
| `wilkinson_40` | 41 | 40 | 38 | 8.257 ms | 501.363 us | 8.759 ms | 40 | 40 |  |
| `wilkinson_40` | 43 | 40 | 38 | 8.254 ms | 500.062 us | 8.754 ms | 40 | 40 |  |
| `wilkinson_40` | 47 | 40 | 37 | 8.350 ms | 506.732 us | 8.856 ms | 40 | 40 | yes |
| `wilkinson_48` | 53 | 48 | 45 | 17.908 ms | 749.432 us | 18.657 ms | 48 | 48 |  |
| `wilkinson_48` | 59 | 48 | 44 | 18.112 ms | 758.495 us | 18.870 ms | 48 | 48 |  |
| `wilkinson_48` | 61 | 48 | 43 | 18.064 ms | 747.298 us | 18.811 ms | 48 | 48 | yes |
| `wilkinson_56` | 59 | 56 | 53 | 23.836 ms | 1.026 ms | 24.862 ms | 56 | 56 |  |
| `wilkinson_56` | 61 | 56 | 52 | 23.694 ms | 1.024 ms | 24.718 ms | 56 | 56 |  |
| `wilkinson_56` | 67 | 56 | 51 | 24.123 ms | 1.040 ms | 25.163 ms | 56 | 56 | yes |
| `legendre_P30` | 61 | 15 | 15 | 1.055 ms | 39.961 ms | 41.016 ms | 16,384 | 1 |  |
| `legendre_P30` | 67 | 7 | 15 | 1.397 ms | 177.273 us | 1.574 ms | 64 | 1 |  |
| `legendre_P30` | 71 | 4 | 15 | 484.138 us | 69.644 us | 553.782 us | 8 | 1 | yes |
| `xpow24_minus1` | 5 | 14 | 11 | 397.750 us | 1.078 ms | 1.476 ms | 150 | 77 |  |
| `xpow24_minus1` | 7 | 15 | 9 | 379.283 us | 155.140 us | 534.423 us | 38 | 20 |  |
| `xpow24_minus1` | 11 | 13 | 7 | 322.097 us | 1.778 ms | 2.100 ms | 113 | 113 | yes |

Rows where the walk retained a single prime, for completeness:

| instance | prime | local factors | Hensel precision | downstream lift | downstream recombination | downstream total |
|---|---:|---:|---:|---:|---:|---:|
| `cyclo_phi179` | 3 | 2 | 113 | 59.749 ms | 5.740 ms | 65.489 ms |
| `cyclo_phi128_x_phi165` | 7 | 8 | 52 | 65.236 ms | 41.284 ms | 106.520 ms |
| `cyclo_phi385` | 3 | 4 | 152 | 166.623 ms | 82.158 ms | 248.782 ms |
| `chebyshev_T24` | 5 | 3 | 22 | 149.933 us | 25.538 us | 175.471 us |
| `chebyshev_U24` | 3 | 4 | 33 | 306.284 us | 24.927 us | 331.211 us |
| `legendre_P38` | 79 | 3 | 19 | 689.002 us | 50.865 us | 739.867 us |
| `cyclo_phi17` | 3 | 1 | 11 | 3.595 us | 6.450 us | 10.045 us |
| `cyclo_phi41` | 3 | 5 | 26 | 725.966 us | 1.460 ms | 2.186 ms |
| `randprod_10` | 7 | 4 | 11 | 197.793 us | 21.712 us | 219.505 us |
| `randprod_21` | 17 | 7 | 9 | 350.950 us | 39.859 us | 390.809 us |

### Modular sub-phases at the selected prime

A repeat of the modular factorization at the already-selected prime, run after
the cascade. `berlekampFactor` recomputes the fixed-space kernel internally, so
equal-degree splitting is its total less the separately measured matrix
construction and row reduction. The production route splits from that kernel
and never runs distinct-degree factorization, so there is no distinct-degree
stage to attribute.

| instance | prime | modular degree | kernel dimension | modular image | good-prime test | Berlekamp matrix | row reduction | equal-degree splitting | full split |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 29 | 32 | 16 | 2.033 us | 19.899 us | 2.003 us | 1.561 ms | 1.969 ms | 3.533 ms |
| `sd5_shift1` | 29 | 32 | 16 | 2.364 us | 34.801 us | 1.893 us | 2.258 ms | 1.409 ms | 3.669 ms |
| `sd5_shift2` | 29 | 32 | 16 | 2.854 us | 33.840 us | 2.234 us | 2.252 ms | 2.896 ms | 5.150 ms |
| `sd4_x_sd4shift1` | 29 | 32 | 16 | 2.643 us | 34.331 us | 1.702 us | 2.266 ms | 2.281 ms | 4.548 ms |
| `sd5_x_phi11` | 29 | 42 | 17 | 2.974 us | 52.277 us | 2.443 us | 4.548 ms | 4.432 ms | 8.982 ms |
| `xpow48_minus1` | 11 | 48 | 19 | 1.302 us | 6.109 us | 2.323 us | 730.734 us | 1.356 ms | 2.089 ms |
| `xpow105_minus1` | 17 | 105 | 14 | 2.664 us | 12.298 us | 5.318 us | 4.958 ms | 4.971 ms | 9.934 ms |
| `xpow120_minus1` | 7 | 120 | 39 | 4.757 us | 16.324 us | 13.631 us | 3.811 ms | 12.961 ms | 16.786 ms |
| `cyclo_phi179` | 3 | 178 | 2 | 4.166 us | 35.593 us | 8.623 us | 13.892 ms | 945.803 us | 14.847 ms |
| `cyclo_phi64_x_phi105` | 11 | 80 | 10 | 2.284 us | 162.240 us | 4.747 us | 18.393 ms | 3.055 ms | 21.453 ms |
| `cyclo_phi128_x_phi165` | 7 | 144 | 8 | 3.665 us | 442.847 us | 7.371 us | 88.494 ms | 6.946 ms | 95.448 ms |
| `cyclo_phi385` | 3 | 240 | 4 | 5.859 us | 717.164 us | 15.102 us | 200.957 ms | 5.446 ms | 206.418 ms |
| `wilkinson_40` | 47 | 40 | 40 | 2.784 us | 20.099 us | 1.922 us | 251.153 us | 1.559 ms | 1.812 ms |
| `wilkinson_48` | 61 | 48 | 48 | 3.305 us | 35.232 us | 2.214 us | 360.775 us | 2.507 ms | 2.870 ms |
| `wilkinson_56` | 67 | 56 | 56 | 4.076 us | 36.745 us | 2.594 us | 561.713 us | 3.781 ms | 4.346 ms |
| `chebyshev_T24` | 5 | 24 | 3 | 711 ns | 11.827 us | 1.042 us | 282.409 us | 38.426 us | 321.877 us |
| `chebyshev_U24` | 3 | 24 | 4 | 771 ns | 6.039 us | 1.062 us | 235.148 us | 75.683 us | 311.893 us |
| `legendre_P30` | 71 | 30 | 4 | 1.523 us | 17.586 us | 1.412 us | 1.700 ms | 409.147 us | 2.111 ms |
| `legendre_P38` | 79 | 38 | 3 | 1.832 us | 25.659 us | 1.772 us | 3.540 ms | 152.367 us | 3.694 ms |
| `cyclo_phi17` | 3 | 16 | 1 | 450 ns | 3.796 us | 681 ns | 98.566 us | 0 ns | 95.151 us |
| `cyclo_phi41` | 3 | 40 | 5 | 1.041 us | 8.954 us | 1.853 us | 457.949 us | 227.558 us | 687.360 us |
| `xpow24_minus1` | 11 | 24 | 13 | 721 ns | 3.435 us | 1.152 us | 190.653 us | 423.057 us | 614.862 us |
| `randprod_10` | 7 | 20 | 4 | 671 ns | 12.368 us | 822 ns | 410.518 us | 119.418 us | 530.758 us |
| `randprod_21` | 17 | 24 | 7 | 882 ns | 19.188 us | 1.152 us | 1.001 ms | 211.854 us | 1.214 ms |

Which stage dominates is decided by the kernel dimension, not by the degree.
Row reduction is 93.6%, 92.7%, 97.4% and 85.7% of the Berlekamp call on
`cyclo_phi179`, `cyclo_phi128_x_phi165`, `cyclo_phi385` and
`cyclo_phi64_x_phi105` -- wide matrices with 2, 8, 4 and 10 dimensional kernels.
Equal-degree splitting dominates instead where the kernel is large: 87.0% on
`wilkinson_56` (kernel 56 of degree 56), 77.2% on `xpow120_minus1` (39 of 120),
and 55.8% on `sd5` (16 of 32). Berlekamp matrix construction is negligible
everywhere, single-digit microseconds on every row.

### Hensel lift

`balancedSplitIndex` halves the factor list by count, except when one modular
factor carries more than half the total degree, where it picks the least
degree-imbalanced prefix instead. Either way the product tree is binary with
one `henselLiftFactors` call per internal node -- `local factors - 1` of them,
as recorded above. The two Hensel-bound rows are the two with few, wide local
factors at a small prime: `cyclo_phi179` lifts 2 factors of degree 89 to
`3^113`, and `cyclo_phi385` lifts 4 factors of degree 60 to `3^152`.

## Cactus ranks 118--144

A cactus curve sorts each system's own solved instances by time, so rank `k`
names a different instance for each system. The two readings are kept apart.

Hex solves 144 of the 160 combined rows; verified Isabelle BZ solves 141.

### Cumulative-rank view (independently sorted, as plotted)

| rank | hex-factor instance | time | cumulative | isabelle-bz instance | time | cumulative |
|---:|---|---:|---:|---|---:|---:|
| 118 | `wilkinson_28` | 7.507 ms | 106.356 ms | `legendre_P38` | 6.723 ms | 128.506 ms |
| 119 | `cyclo_phi24_x_phi35` | 8.875 ms | 115.231 ms | `cyclo_phi24_x_phi35` | 6.782 ms | 135.288 ms |
| 120 | `wilkinson_32` | 9.747 ms | 124.978 ms | `xpow48_minus1` | 8.392 ms | 143.680 ms |
| 121 | `sd4_x_phi17` | 10.242 ms | 135.219 ms | `laguerre_L32` | 8.421 ms | 152.101 ms |
| 122 | `xpow60_minus1` | 13.519 ms | 148.738 ms | `wilkinson_40` | 10.286 ms | 162.387 ms |
| 123 | `wilkinson_40` | 15.912 ms | 164.650 ms | `sd4_x_sd4shift1` | 10.803 ms | 173.190 ms |
| 124 | `sd4_x_phi35` | 20.764 ms | 185.415 ms | `xpow60_minus1` | 10.999 ms | 184.189 ms |
| 125 | `xpow48_minus1` | 21.635 ms | 207.050 ms | `wilkinson_48` | 14.492 ms | 198.681 ms |
| 126 | `sd4_x_sd4shift1` | 25.091 ms | 232.141 ms | `sd5_shift2` | 14.716 ms | 213.396 ms |
| 127 | `wilkinson_48` | 29.732 ms | 261.873 ms | `sd5_shift1` | 14.815 ms | 228.211 ms |
| 128 | `wilkinson_56` | 40.396 ms | 302.269 ms | `cyclo_phi179` | 14.956 ms | 243.167 ms |
| 129 | `cyclo_phi151` | 73.132 ms | 375.401 ms | `wilkinson_56` | 21.980 ms | 265.147 ms |
| 130 | `cyclo_phi179` | 80.025 ms | 455.426 ms | `sd5` | 22.610 ms | 287.757 ms |
| 131 | `xpow105_minus1` | 84.464 ms | 539.890 ms | `sd4_x_phi35` | 26.190 ms | 313.947 ms |
| 132 | `cyclo_phi64_x_phi105` | 88.460 ms | 628.350 ms | `sd5_x_phi11` | 27.545 ms | 341.492 ms |
| 133 | `sd5_shift1` | 96.670 ms | 725.020 ms | `cyclo_phi64_x_phi105` | 37.990 ms | 379.483 ms |
| 134 | `sd5_shift2` | 99.713 ms | 824.733 ms | `cyclo_phi89` | 52.018 ms | 431.501 ms |
| 135 | `sd5` | 106.911 ms | 931.644 ms | `xpow105_minus1` | 55.922 ms | 487.423 ms |
| 136 | `cyclo_phi625` | 184.726 ms | 1.116 s | `xpow120_minus1` | 168.811 ms | 656.234 ms |
| 137 | `cyclo_phi128_x_phi165` | 205.261 ms | 1.322 s | `cyclo_phi625` | 171.217 ms | 827.451 ms |
| 138 | `sd5_x_phi11` | 222.540 ms | 1.544 s | `cyclo_phi128_x_phi165` | 172.600 ms | 1.000 s |
| 139 | `cyclo_phi385` | 455.841 ms | 2.000 s | `cyclo_phi385` | 355.307 ms | 1.355 s |
| 140 | `sd5_x_phi45` | 514.710 ms | 2.515 s | `cyclo_phi151` | 528.715 ms | 1.884 s |
| 141 | `xpow120_minus1` | 523.812 ms | 3.039 s | `cyclo_phi1031` | 8.179 s | 10.064 s |
| 142 | `hoeij_M12_f132` | 1.665 s | 4.703 s | -- | -- | -- |
| 143 | `hoeij_F190` | 7.238 s | 11.942 s | -- | -- | -- |
| 144 | `sd6` | 8.115 s | 20.057 s | -- | -- | -- |

Cumulative parity is at rank 124 (185.415 ms against 184.189 ms). The ratio
peaks near rank 135 (931.644 ms against 487.423 ms, 1.91x) and Hex retakes the
lead at rank 141, where Isabelle's `cyclo_phi1031` costs 8.179 s.

### Paired-testcase view (same instance, both systems)

| hex-factor rank | instance | degree | hex-factor | isabelle-bz | isabelle-bz / hex-factor |
|---:|---|---:|---:|---:|---:|
| 118 | `wilkinson_28` | 28 | 7.507 ms | 4.036 ms | 0.54x |
| 119 | `cyclo_phi24_x_phi35` | 32 | 8.875 ms | 6.782 ms | 0.76x |
| 120 | `wilkinson_32` | 32 | 9.747 ms | 6.075 ms | 0.62x |
| 121 | `sd4_x_phi17` | 32 | 10.242 ms | 4.567 ms | 0.45x |
| 122 | `xpow60_minus1` | 60 | 13.519 ms | 10.999 ms | 0.81x |
| 123 | `wilkinson_40` | 40 | 15.912 ms | 10.286 ms | 0.65x |
| 124 | `sd4_x_phi35` | 40 | 20.764 ms | 26.190 ms | 1.26x |
| 125 | `xpow48_minus1` | 48 | 21.635 ms | 8.392 ms | 0.39x |
| 126 | `sd4_x_sd4shift1` | 32 | 25.091 ms | 10.803 ms | 0.43x |
| 127 | `wilkinson_48` | 48 | 29.732 ms | 14.492 ms | 0.49x |
| 128 | `wilkinson_56` | 56 | 40.396 ms | 21.980 ms | 0.54x |
| 129 | `cyclo_phi151` | 150 | 73.132 ms | 528.715 ms | 7.23x |
| 130 | `cyclo_phi179` | 178 | 80.025 ms | 14.956 ms | 0.19x |
| 131 | `xpow105_minus1` | 105 | 84.464 ms | 55.922 ms | 0.66x |
| 132 | `cyclo_phi64_x_phi105` | 80 | 88.460 ms | 37.990 ms | 0.43x |
| 133 | `sd5_shift1` | 32 | 96.670 ms | 14.815 ms | 0.15x |
| 134 | `sd5_shift2` | 32 | 99.713 ms | 14.716 ms | 0.15x |
| 135 | `sd5` | 32 | 106.911 ms | 22.610 ms | 0.21x |
| 136 | `cyclo_phi625` | 500 | 184.726 ms | 171.217 ms | 0.93x |
| 137 | `cyclo_phi128_x_phi165` | 144 | 205.261 ms | 172.600 ms | 0.84x |
| 138 | `sd5_x_phi11` | 42 | 222.540 ms | 27.545 ms | 0.12x |
| 139 | `cyclo_phi385` | 240 | 455.841 ms | 355.307 ms | 0.78x |
| 140 | `sd5_x_phi45` | 56 | 514.710 ms | timeout | -- |
| 141 | `xpow120_minus1` | 120 | 523.812 ms | 168.811 ms | 0.32x |
| 142 | `hoeij_M12_f132` | 132 | 1.665 s | timeout | -- |
| 143 | `hoeij_F190` | 190 | 7.238 s | timeout | -- |
| 144 | `sd6` | 64 | 8.115 s | timeout | -- |

The paired view is the one an attribution argument needs, and it disagrees with
the cumulative view about which rows matter. `cyclo_phi151` is a 7.23x Hex
*win* sitting inside the elbow; `cyclo_phi625` and `cyclo_phi128_x_phi165` are
near parity. The genuine paired losses are the Swinnerton-Dyer group
(0.12x-0.21x on `sd5`, its shifts and `sd5_x_phi11`; 0.43x on
`sd4_x_sd4shift1`), `cyclo_phi179` (0.19x), `xpow48_minus1` (0.39x),
`xpow120_minus1` (0.32x), `cyclo_phi64_x_phi105` (0.43x), and the Wilkinson
group (0.49x-0.65x across degrees 28 through 56).

Aggregated over the whole 392-row corpus, on the 216 rows where both systems
answer above ten times their own protocol overhead, Hex divided by verified
Isabelle BZ has median 0.754x, p10-p90 0.467x-2.713x, and a 134-82 win split.

## Sampling profiles

Leaf-cost categorisation, in the four categories `SPEC/profiling.md` fixes.
Percentages are of retained samples on the service's main thread.

| instance | samples | replays | Lean own code | GMP | allocation / free | Lean runtime | classified |
|---|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 6,227 | 58 | 5.5% | 13.3% | 69.1% | 8.7% | 96.63% |
| `sd5_x_phi11` | 6,064 | 27 | 4.6% | 15.3% | 66.3% | 10.3% | 96.55% |
| `xpow120_minus1` | 5,815 | 11 | 3.8% | 22.5% | 61.9% | 7.4% | 95.67% |
| `cyclo_phi179` | 6,104 | 75 | 5.5% | 16.7% | 56.9% | 16.0% | 95.09% |
| `cyclo_phi64_x_phi105` | 6,079 | 69 | 19.7% | 3.6% | 35.6% | 34.0% | 93.03% |
| `cyclo_phi385` | 5,952 | 13 | 11.0% | 16.0% | 44.7% | 23.8% | 95.46% |
| `wilkinson_56` | 6,144 | 150 | 11.2% | 13.2% | 50.3% | 17.8% | 92.37% |
| `xpow48_minus1` | 5,984 | 263 | 9.3% | 13.5% | 56.7% | 14.4% | 94.0% |
| `xpow105_minus1` | 6,059 | 72 | 14.6% | 13.7% | 45.2% | 20.2% | 93.76% |

Inclusive share of the production cascade, by Hex function. `Hex.classicalInput`
is the whole bounded prime walk; `Hex.henselLiftData` is the multifactor lift;
`Hex.scanDirectCombinations` is the head-forced recombination traversal;
`Hex.exactQuotient?` is exact integer polynomial division.

| instance | `Hex.classicalInput` | `Hex.Berlekamp.berlekampFactor` | `Hex.Matrix.rowReduce` | `Hex.henselLiftData` | `Hex.ZPoly.reduceModPowImpl` | `Hex.proposeFactorization` | `Hex.scanDirectCombinations` | `Hex.tryDirectCandidate` | `Hex.directCandidate` | `Hex.exactQuotient?` |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `sd5` | 8.9% | 8.8% | 1.0% | 1.7% | 0.6% | <0.5% | 85.6% | 30.1% | 4.4% | 6.6% |
| `sd5_x_phi11` | 9.9% | 9.7% | 2.1% | 1.4% | <0.5% | <0.5% | 86.5% | 36.4% | 5.2% | 10.5% |
| `xpow120_minus1` | 12.3% | 12.2% | 0.6% | 4.0% | 1.1% | <0.5% | 77.9% | 77.5% | 12.8% | 64.0% |
| `cyclo_phi179` | 18.6% | 18.5% | 12.4% | 73.2% | 21.0% | <0.5% | 5.5% | 5.5% | 1.1% | 4.4% |
| `cyclo_phi64_x_phi105` | 85.0% | 83.8% | 49.7% | 8.8% | 2.4% | <0.5% | 5.5% | 5.4% | 1.8% | 3.5% |
| `cyclo_phi385` | 44.8% | 44.4% | 41.3% | 36.2% | 11.6% | <0.5% | 11.7% | 11.7% | 1.6% | 10.2% |
| `wilkinson_56` | 35.0% | 32.0% | <0.5% | 57.0% | 20.2% | 62.9% | <0.5% | <0.5% | <0.5% | 2.1% |
| `xpow48_minus1` | 27.9% | 27.3% | 2.0% | 5.2% | <0.5% | <0.5% | 65.1% | 64.6% | 11.6% | 52.0% |
| `xpow105_minus1` | 47.3% | 46.9% | 3.9% | 18.0% | 4.2% | <0.5% | 30.6% | 30.5% | 2.7% | 27.8% |

Top self-time leaves:

- `sd5`: `int_free_chunk` 20.3%, `_realloc` 16.4%, `int_malloc` 8.7%, `mi_free` 5.5%, `mi_malloc_small` 5.3%.
- `sd5_x_phi11`: `int_free_chunk` 17.7%, `_realloc` 15.1%, `int_malloc` 7.0%, `_GI___libc_malloc` 6.3%, `mi_free` 6.0%.
- `xpow120_minus1`: `_realloc` 17.5%, `int_free_chunk` 15.0%, `_libc_malloc2` 7.5%, `_gmpn_copyi_x86_64` 6.8%, `int_malloc` 4.8%.
- `cyclo_phi179`: `int_free_chunk` 13.2%, `_realloc` 11.1%, `_GI___libc_malloc` 7.7%, `int_malloc` 6.8%, `_free` 4.8%.
- `cyclo_phi64_x_phi105`: `mi_malloc_small` 13.7%, `mi_free` 13.1%, `Fin.foldl.loop` 8.8%, `Hex.Matrix.rowAdd` 7.8%, `lean_apply_2` 5.3%.
- `cyclo_phi385`: `int_free_chunk` 9.1%, `Fin.foldl.loop` 8.8%, `mi_malloc_small` 7.8%, `Hex.Matrix.rowAdd` 7.7%, `mi_free` 6.9%.
- `wilkinson_56`: `int_free_chunk` 10.1%, `_realloc` 8.7%, `mi_malloc_small` 6.2%, `mi_free` 5.8%, `_GI___libc_malloc` 5.7%.
- `xpow48_minus1`: `_realloc` 13.0%, `int_free_chunk` 12.6%, `mi_malloc_small` 6.4%, `_GI___libc_malloc` 5.3%, `mi_free` 4.8%.
- `xpow105_minus1`: `_realloc` 8.9%, `mi_malloc_small` 8.3%, `mi_free` 7.5%, `int_free_chunk` 6.7%, `lean_apply_2` 5.2%.

Allocation is the largest single leaf category on all nine profiles, between
35.6% and 69.1%. It is not confined to one phase: the recombination-bound rows
spend it in `int_free_chunk` and `_realloc` under candidate construction and
exact division, while `cyclo_phi64_x_phi105` and `cyclo_phi385` spend it in
`mi_malloc_small`/`mi_free` under `Hex.Matrix.rowAdd`. GMP is a distant second
and peaks at 22.5% on `xpow120_minus1`, whose exact divisions are dense bignum
long division.

The phase table and the profiles agree everywhere they overlap: `sd5` is 88.9%
recombination against 85.6% under `scanDirectCombinations`, `cyclo_phi179`
74.4% Hensel against 73.2% under `henselLiftData`, `cyclo_phi64_x_phi105` 85.1%
prime walk against 85.0% under `classicalInput`.

## Go / no-go for the dependent issues

### #9128 -- scout modular degree patterns before full splitting: **go**

Confirmed by the counterfactual table, with two corrections to the issue's
framing.

The waste it names is real: on `sd5` and its shifts, on Wilkinson 40/48/56, and
on `xpow120_minus1`, the two extra full Berlekamp factorizations change neither
the local factor count nor the downstream choice. But the prize must be
measured as *avoidable extra splitting*, not as the prime-walk share. On that
basis the material rows are `cyclo_phi64_x_phi105` (60.5% of total),
`xpow105_minus1` (34.8%), `wilkinson_40`/`48`/`56` (26.5%, 22.4%, 23.7%),
`sd4_x_sd4shift1` (21.9%), and `xpow48_minus1` (19.3%). `cyclo_phi179`,
`cyclo_phi128_x_phi165`, and `cyclo_phi385` retain one prime and have no prize
at all, so a scout must not be evaluated on them.

Against the measured bounded oracle -- the "downstream total" column -- the
production selection is within 5% on 11 of the 12 multi-prime representative
rows. The exception is `xpow48_minus1` at 1.308x, so there is a second, smaller
prize in the choice itself, not only in the cost of making it.
`xpow105_minus1`, `xpow120_minus1`, and `legendre_P30` are the rows that forbid
a first-good-prime rule: their rejected candidates cost 41.016 ms to 36.732 s
downstream, against 553.782 us to 463.253 ms for the plans actually selected.

Two of the issue's stated widths reproduce (`cyclo_phi64_x_phi105` at 10, 14,
12 and `xpow105_minus1` at 30, 33, 14) and one does not: it gives
`xpow120_minus1` as 39, 64, 42, where this record measures 39, 65, 42.

### #9129 -- enumerate factor supports without allocating lists: **go**

Confirmed, and the profiles locate the cost more precisely than the issue does.
`Hex.scanDirectCombinations` is 85.6% inclusive on `sd5` and 86.5% on
`sd5_x_phi11`, while `Hex.tryDirectCandidate` -- everything from the degree
filter inwards -- is only 30.1% and 36.4%. **The remaining 55.5% and 50.1% is
the traversal itself**: reversing selected indices, reversing and concatenating
rejected indices, and building the selected-factor list at each of the 32,768
and 65,522 leaves. Allocation is 69.1% and 66.3% of sampled leaves, above the
37-64% the issue quotes.

The contrast with the other recombination-bound rows makes the point. On
`xpow48_minus1`, `xpow105_minus1`, and `xpow120_minus1` the same difference is
0.5%, 0.1%, and 0.4%, because their cheap filters reject nothing and every leaf
proceeds into the candidate test anyway. The support cursor is a
Swinnerton-Dyer optimization specifically.

### #9130 -- reject impossible exact divisors over a word-sized prime: **go**

Confirmed. `Hex.exactQuotient?` inclusive share is 64.0% on `xpow120_minus1`
(the issue says about 63%), 52.0% on `xpow48_minus1`, and 27.8% on
`xpow105_minus1` (the issue says about 31%). The counters give the rejection
headroom directly: `xpow48_minus1` attempts 268 divisions of which 10 succeed
(96.3% rejectable), `xpow105_minus1` 60 of which 8 succeed (86.7%), and
`xpow120_minus1` 1,801 of which 16 succeed (99.1%). A necessary-condition
filter therefore has 87%-99% of the divisions available to reject on exactly
the rows the issue names. On `xpow48_minus1` and `xpow105_minus1` the existing
cheap filters reject nothing at all, so every one of those divisions is
reachable; on `xpow120_minus1` they already reject 3,538 of 5,339 leaves and
the 1,801 survivors are what remains.

### #9131 -- keep quadratic Hensel lifts canonical: **go**

Confirmed. `Hex.henselLiftData` is 73.2% inclusive on `cyclo_phi179` (the issue
says about 73%) and 57.0% on `wilkinson_56` (about 58%).
`Hex.ZPoly.reduceModPowImpl` is 21.0% and 20.2% of *total* time on those rows,
which is 29% and 35% of lift time -- higher than the "roughly 20% of lift time"
the issue estimates, so Phase 1 of that issue has more headroom than stated.
`cyclo_phi385` adds a third row at 36.2% lift and 11.6% `reduceModPow`.

Two refinements. The Wilkinson rows answer from the proposal-replay tier, not
the classical tier, so their lift happens inside `proposeFactorization` (62.9%
inclusive) rather than in the cascade's own Hensel phase, and Phase 1's audit
must cover that call path. And the product tree is count-balanced with a
guarded dominant-degree split, not degree-balanced throughout: the audit's
invariant statement should follow `balancedSplitIndex` rather than assume a
degree-balanced tree.

### #9132 -- packed finite-field matrix: **go to the measurement gate, with a caveat**

`Hex.Matrix.rowReduce` is 41.3% inclusive on `cyclo_phi385` and 49.7% on
`cyclo_phi64_x_phi105`, matching the issue's 40% and 50%. But the two rows are
not equivalent evidence, and the issue is right to make #9128 come first:

- `cyclo_phi385` retains **one** prime, so its 41.3% is row reduction at the
  selected prime and survives any change to the walk. Against the issue's gate
  it is already 41.3% of total factor time and 204.678 ms of a 206.418 ms
  selected-prime Berlekamp call (97.4%).
- `cyclo_phi64_x_phi105` retains **three** primes, so most of its 49.7% is row
  reduction at primes the plan discards. After #9128 that row is expected to
  fall below the gate.

`cyclo_phi128_x_phi165` is a second single-prime witness: 97.186 ms of prime
walk of which 95.448 ms is the one Berlekamp call, 92.7% of it row reduction.
Remeasure after #9128 as the issue requires; the single-prime rows are the ones
that will still support the gate. The modular sub-phase table also gives the
gate a sharper predictor than degree: row reduction dominates when the
fixed-space kernel is small relative to the modular degree, and equal-degree
splitting dominates when it is large.

### #9133 -- iterated quadratic norm certificates: **defer as designed**

The baseline the issue asks for is recorded. `sd5` costs 103.698 ms with 16
local factors, 32,768 recombination nodes, 32,639 cheap-filter rejections, 129
exact divisions and one successful divisor; `sd5_x_phi11` costs 213.179 ms with
65,522 nodes; `sd4_x_sd4shift1` costs 23.575 ms with 10,540 nodes; `sd6` is a
solved 8.115 s row at cactus rank 144. The paired Isabelle gap is 0.12x on
`sd5_x_phi11`, 0.15x on both `sd5` shifts, 0.21x on `sd5`, and 0.43x on
`sd4_x_sd4shift1` -- the worst group in the corpus. These records carry no
Isabelle-side traversal counters, so they cannot settle whether Isabelle
examines a comparable number of supports; what they do show is that 55.5% of
`sd5` is support traversal outside the candidate test, which is #9129's target.
Re-evaluate after #9129 and #9130 land, as the issue specifies; nothing here
justifies starting the certificate work now.

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
