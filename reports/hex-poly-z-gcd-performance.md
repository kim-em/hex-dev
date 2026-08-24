# HexPolyZGcd Performance Report

## Bench Targets

The Mathlib-free suite is registered in `bench/HexPolyZGcd/Bench.lean`.
Polynomial construction, deterministic random-word generation, and denominator
scaling occur in `prep` functions outside the timed region; every target hashes
the complete result inside the benchmark harness.

| target | input family | declared model |
|---|---|---|
| `runCoprimeImage` | `coprime-pairs` | `n * n` |
| `runCoprimeGcd` | `coprime-pairs` | `n * n` |
| `runDense8` | `dense-gcds` | `n * n` |
| `runDense256` | `dense-gcds` | `n * n` |
| `runSwellPrs` | `swell` | `bits * Nat.sqrt bits` |
| `runSqfFast` | `squarefree` | `n * n` |
| `runRatGcd` | `rational` | `n * n` |

The coefficient generator is deterministic SplitMix (`HexBasic.Rand`) keyed by
degree, coefficient index, bit width, and salt; there is no ambient random seed.
The coprime pair uses salts 11 and 19. Dense gcds use salt 31 for the common
factor and 47/59 for the two cofactors. The swell case uses salts 71 and 89.
`prepSquarefree n` deterministically multiplies one repeated linear factor and
the `n` distinct factors with constants 2 through `n + 1`. `prepRational` scales
the deterministic 8-bit dense inputs by 1/101 and 1/103.

Fixed registrations cover three additional comparisons on the exact same
prepared inputs:

| comparison | registered ladder |
|---|---|
| public `gcd` / FLINT `fmpz_poly_gcd` | coprime, dense-8, dense-256 at degrees 64, 128, 256, 512 |
| public `gcd` / `DensePoly Rat` Euclidean reference | coprime 16, 32, 64; dense-8 16, 32, 64, 128; dense-256 16, 32; swell at 512 coefficient bits |
| `ZPoly.sqfDecomp` / `primitiveSquareFreeDecomposition` | factor counts 2, 4, 8, 16, 32, 64, 128 |

The FLINT side uses the shared persistent-subprocess driver
`scripts/oracle/flint_bench_driver.py`; its `fmpz_poly/gcd` operation constructs
python-flint `fmpz_poly` values and calls `fmpz_poly.gcd`.

## Verdicts

The native scientific run used clean commit
`cccbc44e5f4ad75ae3f21ad70db787dbaafa7c51` on `chungus2` (AMD EPYC
9455 48-Core Processor, x86-64 Linux), Lean `4.34.0-rc2`, and lean-bench
`0.1.0`. The command was:

```sh
lake exe hexpolyzgcd_bench run \
  Hex.PolyZGcdBench.runCoprimeImage \
  Hex.PolyZGcdBench.runCoprimeGcd \
  Hex.PolyZGcdBench.runDense8 \
  Hex.PolyZGcdBench.runDense256 \
  Hex.PolyZGcdBench.runSwellPrs \
  Hex.PolyZGcdBench.runSqfFast \
  Hex.PolyZGcdBench.runRatGcd \
  --outer-trials 1 \
  --export-file reports/bench-results/hex-poly-z-gcd-native-cccbc44e-chungus2.json
```

The export has SHA-256
`86d099684098923f738c083a61fe8119424e56811e4c143770f4e24899f87578`.
The first and last medians below are the JSON `trial_summaries` rows; `β` and
the normalized-cost interval are the export's fitted verdict fields.

| target | successful rungs | first → last median | residual slope β | normalized cost | verdict |
|---|---:|---:|---:|---:|---|
| `runCoprimeImage` | 8…8192 | 0.008698 → 2,680.883 ms | −0.003 | 37.331…41.725 | consistent with declared complexity |
| `runCoprimeGcd` | 8…4096 | 0.063524 → 4,249.508 ms | −0.014 | 241.211…261.592 | consistent with declared complexity |
| `runDense8` | 16…4096 | 0.111270 → 1,635.700 ms | −0.057 | 85.852…112.155 | consistent with declared complexity |
| `runDense256` | 16…2048 | 1.475710 → 8,134.175 ms | +0.003 | 1,926.441…1,968.851 | consistent with declared complexity |
| `runSwellPrs` | 8…32768 bits | 0.383321 → 4,519.497 ms | −0.173 | 762.012…4,202.881 | consistent with declared complexity |
| `runSqfFast` | 2…2048 | 0.012661 → 2,117.396 ms | −0.056 | 473.019…619.463 | consistent with declared complexity |
| `runRatGcd` | 8…4096 | 0.056946 → 1,681.171 ms | −0.105 | 85.387…140.876 | consistent with declared complexity |

`runCoprimeImage`, `runCoprimeGcd`, and `runDense256` stopped at the
ten-second cap on their next scheduled rung; this is recorded as
`truncated_at_cap`, not as a complexity failure. The other four schedules
completed. Every successful rung emitted a stable result hash.

The internal fixed run used clean commit
`f0fcf49ecd16eda0556589a9d6e6a67c394fd57f` on the same host and
toolchain. It ran the fixed names in the second table above with five repeats
and wrote
`reports/bench-results/hex-poly-z-gcd-internal-f0fcf49e-chungus2.json`
(SHA-256
`25aad7824ac038abeb91ee12637a58754cc83bf62a7ce2e436058b175da7698e`).
All paired observed hashes agreed. Medians and reference/Hex speedups were:

| family | parameter | Hex median | reference median | reference / Hex |
|---|---:|---:|---:|---:|
| coprime | 16 | 0.155715 ms | 1.834992 ms | 11.784× |
| coprime | 32 | 0.424629 ms | 22.960726 ms | 54.072× |
| coprime | 64 | 1.347243 ms | 588.704920 ms | 436.970× |
| dense-8 | 16 | 0.107064 ms | 0.456946 ms | 4.268× |
| dense-8 | 32 | 0.304820 ms | 6.403622 ms | 21.008× |
| dense-8 | 64 | 0.743874 ms | 103.371063 ms | 138.963× |
| dense-8 | 128 | 2.031435 ms | 3,264.762808 ms | 1,607.121× |
| dense-256 | 16 | 1.511768 ms | 21.121636 ms | 13.971× |
| dense-256 | 32 | 3.674391 ms | 571.783606 ms | 155.613× |
| swell | 512 bits | 0.287630 ms | 100.188759 ms | 348.325× |
| squarefree | 2 | 0.013446 ms | 0.019730 ms | 1.467× |
| squarefree | 4 | 0.026742 ms | 0.034041 ms | 1.273× |
| squarefree | 8 | 0.082721 ms | 0.146461 ms | 1.771× |
| squarefree | 16 | 0.245746 ms | 0.676459 ms | 2.753× |
| squarefree | 32 | 0.848389 ms | 5.038558 ms | 5.939× |
| squarefree | 64 | 3.490955 ms | 54.390429 ms | 15.580× |
| squarefree | 128 | 10.566782 ms | 892.173124 ms | 84.432× |

Thus the integer gcd beats the rational Euclidean reference at every registered
family and rung, including by well over the required 10× on the swell case.
The new squarefree entry point beats the former rational implementation at
every rung, with a widening advantage after factor count 16.

## Comparator Ratios

The gating comparator is **FLINT fmpz_poly_gcd via python-flint**. The clean
run used python-flint `0.9.0`, commit
`ab45c5ef71fdeeedca58344630a85d16503fbb8b`, the same host/toolchain,
and this command shape (the twelve Lean/FLINT pairs are the registered degrees
64, 128, 256, and 512 for each of the three families):

```sh
HEX_FLINT_BENCH_PYTHON=/tmp/hex-poly-z-gcd-flint/bin/python \
  lake exe hexpolyzgcd_bench run \
  Hex.PolyZGcdBench.runFlintOverhead \
  Hex.PolyZGcdBench.runLeanCoprime{64,128,256,512} \
  Hex.PolyZGcdBench.runFlintCoprime{64,128,256,512} \
  Hex.PolyZGcdBench.runLeanDense8_{64,128,256,512} \
  Hex.PolyZGcdBench.runFlintDense8_{64,128,256,512} \
  Hex.PolyZGcdBench.runLeanDense256_{64,128,256,512} \
  Hex.PolyZGcdBench.runFlintDense256_{64,128,256,512} \
  --export-file reports/bench-results/hex-poly-z-gcd-flint-ab45c5ef-chungus2.json
```

Brace expansion denotes the explicitly registered names. The export has
SHA-256
`954358d739fec98466e1ed72f7462e7d1a6dec675923b1b3c820c9bef30cd501`.
Every Lean/FLINT pair returned the same polynomial hash. The persistent empty
call median was 12.770 µs. All twelve rungs are eligible: overhead is below 50%
of the FLINT median and both per-call medians are below ten seconds. Ratios are
Hex/FLINT; the adjusted value subtracts 12.770 µs from FLINT first.

| family | degree | Hex median | FLINT median | raw ratio | adjusted ratio | eligible |
|---|---:|---:|---:|---:|---:|---|
| coprime-pairs | 64 | 0.139934 ms | 0.060875 ms | 2.299× | 2.909× | yes |
| coprime-pairs | 128 | 0.265369 ms | 0.111892 ms | 2.372× | 2.677× | yes |
| coprime-pairs | 256 | 0.569154 ms | 0.198360 ms | 2.869× | 3.067× | yes |
| coprime-pairs | 512 | 0.965855 ms | 0.362569 ms | 2.664× | 2.761× | yes |
| dense-gcds (8-bit) | 64 | 0.177577 ms | 0.077096 ms | 2.303× | 2.761× | yes |
| dense-gcds (8-bit) | 128 | 0.382643 ms | 0.143531 ms | 2.666× | 2.926× | yes |
| dense-gcds (8-bit) | 256 | 0.792560 ms | 0.266930 ms | 2.969× | 3.118× | yes |
| dense-gcds (8-bit) | 512 | 1.794117 ms | 0.540535 ms | 3.319× | 3.400× | yes |
| dense-gcds (256-bit) | 64 | 0.928786 ms | 8.838583 ms | 0.105× | 0.105× | yes |
| dense-gcds (256-bit) | 128 | 2.240101 ms | 18.152269 ms | 0.123× | 0.124× | yes |
| dense-gcds (256-bit) | 256 | 7.322961 ms | 35.310440 ms | 0.207× | 0.208× | yes |
| dense-gcds (256-bit) | 512 | 22.794512 ms | 73.761656 ms | 0.309× | 0.309× | yes |

The coprime ratio remains in a flat 2.68–3.07× adjusted band across the four
eligible rungs. The dense 8-bit ratio rises mildly from 2.76× to 3.40×, but
remains a small constant with substantial margin to the 5× gate. The 256-bit
family moves from 0.105× to 0.309× as degree grows while Hex remains faster
than the process comparator throughout. At the top eligible rung of every
family, the required Hex/FLINT ratio is below 5×; the gating goal is met.

There is only one declared external comparator, so no comparator-runtime plot
is required.

## Profile

One representative compiled case per declared input family was captured from
clean commit `7f0e536cfe2572165501ee2860cca7c6adc5a261` on `chungus2`
(AMD EPYC 9455, x86-64 Linux 6.12.100), with Lean `4.34.0-rc2`, lean-bench
`0.1.0`, lean-bench-samply
`9356baa2f5757ee40320a897bd284914d5bb9f5e`, samply `0.13.1`, and a
999 Hz sampling rate. Inputs use the deterministic salts listed in Bench
Targets. The command form was:

```sh
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply.SDVVOD/repo \
  scripts/profile/run_profile.sh \
  ./.lake/build/bin/hexpolyzgcd_bench \
  Hex.PolyZGcdBench.TARGET PARAM 5000000000
```

The five `(TARGET, PARAM)` pairs were `(runCoprimeGcd, 4096)`,
`(runDense8, 4096)`, `(runSwellPrs, 32768)`, `(runSqfFast, 2048)`, and
`(runRatGcd, 4096)`. The filtered profiles and symbol sidecars remain at
`/tmp/hex-profile-TARGET-PARAM.json.gz` and are not committed. Leaf categories
classify demangled `Hex.*` and `lean_hex_*` frames as own code, `gmp*`/`mpn*`
frames as GMP, allocator entry points separately, and Lean/std-library frames
as runtime; the residual `other` category is 4.30% or less.

| family / target | own code | GMP | allocation/free | Lean runtime | other |
|---|---:|---:|---:|---:|---:|
| coprime-pairs / `runCoprimeGcd 4096` | 28.33% | 0.07% | 34.79% | 34.31% | 2.49% |
| dense-gcds / `runDense8 4096` | 31.89% | 0.41% | 32.68% | 30.72% | 4.30% |
| swell / `runSwellPrs 32768` | 0.00% | 97.86% | 1.10% | 0.00% | 1.03% |
| squarefree / `runSqfFast 2048` | 19.61% | 31.26% | 24.79% | 20.91% | 3.44% |
| rational / `runRatGcd 4096` | 33.38% | 0.41% | 33.95% | 28.78% | 3.48% |

For coprime pairs, `ZPoly.gcd` covered 100.00% inclusively,
`coprimeCert?`/`reducedGcdCert` 99.98%, `modularWitnessAt` 79.20%,
`DensePoly.mulImpl` 60.20%, `DensePoly.xgcd` 43.39%, and `checkCoprime`
40.35%. This is exactly the registered route-1 target: one modular image and
Bézout witness followed by certificate products and replay.

For dense gcds, `ZPoly.gcd` covered 99.92%, `brownCert?` 99.73%,
`checkedCandidate?` 68.15%, `modularWitnessAt` 51.90%, the dense remainder
step 51.45%, and cached finite-field gcd 45.64%. These costs are the Brown
image/reconstruction, exact candidate division, and certificate replay timed by
the registered dense target.

For swell, `runSwellPrs` covered 66.64%, `prsCert?` 66.62%, the extended
subresultant recurrence 66.57%, `prsCandidate?` 33.99%, and
`prsCoprimeWitness?` 32.65%. Leaf time is almost entirely GMP FFT/basecase
limb arithmetic, matching the large-coefficient fixed-degree PRS model. Missing
parents in the remaining sampled stacks are profiler unwinding through GMP,
not an unregistered preparation phase; timed-region filtering excluded prep.

For squarefree decomposition, `runSqfFast` covered 84.77%, `sqfDecomp`
84.43%, `gcdCert` 84.09%, `brownCert?` 82.33%, `checkedCandidate?` 72.52%,
and `modularWitnessAt` 46.50%. The registered squarefree target is dominated by
the derivative gcd and its checked Brown candidate as intended.

For rational coefficients, `ratGcd` covered 99.94%, `brownCert?` 99.65%,
`checkedCandidate?` 68.05%, the dense remainder step 52.27%,
`modularWitnessAt` 51.66%, and cached finite-field gcd 45.51%. Denominator
clearing is lower order; the registered target is dominated by the resulting
integer gcd.

All filtering runs passed confidence and the ±5 ms sensitivity check:

| target / parameter | residual | timed duration | retained / rejected | other-thread noise | sensitivity |
|---|---:|---:|---:|---:|---|
| `runCoprimeGcd 4096` | 0.217 ms | 4,149.499 ms | 4,010 / 61 | 0 | passed |
| `runDense8 4096` | 0.806 ms | 4,894.811 ms | 4,838 / 200 | 0 | passed |
| `runSwellPrs 32768` | 0.196 ms | 4,455.499 ms | 4,254 / 40 | 0 | passed |
| `runSqfFast 2048` | 0.532 ms | 5,999.899 ms | 5,845 / 2,564 | 0 | passed |
| `runRatGcd 4096` | 0.398 ms | 4,935.514 ms | 4,907 / 114 | 0 | passed |

No dominant inclusive cost lies outside its registered benchmark target.

## Concerns

None.
