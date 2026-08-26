# HexTruncatedSeries Performance Report

`HexTruncatedSeries` implements fixed-precision truncated-series arithmetic.
This report covers the six compiled input families declared in `libraries.yml`:
`multiplication`, `inverse`, `exp-log`, `sqrt`, `composition`, and `reversion`.

The release-quality measurements use clean source revision
`9f031bdf31ef6656ef2e4a56b8ec61d4b6d49fa3` on `chungus2` (AMD EPYC
9455, 96 logical CPUs, x86-64 Linux 6.12.100), Lean `4.34.0-rc2`, and
lean-bench `0.1.0` at commit
`fa30c2763cf523f3ac8e46dc3a1dad0845a40098`.

The committed measurement artefacts are:

| key | artefact | SHA-256 |
|---|---|---|
| P | `reports/bench-results/hex-truncated-series-parametric-9f031bdf-chungus2.json` | `be8e65af1d371eb2dfd9203c6185732bbd37316f96e8ae66bd706a9404a6f961` |
| I | `reports/bench-results/hex-truncated-series-compare-inverse-9f031bdf-chungus2.json` | `5a58062d0fc5a8232702457be388e742dd3a645f7b4d396de9ee934d4a32432a` |
| C | `reports/bench-results/hex-truncated-series-compare-composition-9f031bdf-chungus2.json` | `6c6252ba16126e512ab6b5af3611b563f64e4fe88fca6893ee91b274ae35e65a` |
| R | `reports/bench-results/hex-truncated-series-compare-reversion-9f031bdf-chungus2.json` | `942717e83b169a654b01288982cee41da521e9e979881170a1ce612e1cbef852` |
| F | `reports/bench-results/hex-truncated-series-flint-9f031bdf-chungus2.json` | `c633c00405eab10466f214c252f866046f052e6bc3db35c9ca25d396217e33ab` |

## Bench targets

The parametric registrations and their declared expressions, copied from
`bench/HexTruncatedSeries/Bench.lean`, are:

| target | declared complexity |
|---|---|
| `Hex.TSeriesBench.runMulInt` | `n ^ 2` |
| `Hex.TSeriesBench.runMulRat` | `n ^ 2` |
| `Hex.TSeriesBench.runInverseNewton` | `n ^ 2` |
| `Hex.TSeriesBench.runInverseRecurrence` | `n ^ 2` |
| `Hex.TSeriesBench.runExp` | `n ^ 2 * (Nat.log2 (n + 1) + 1) ^ 2` |
| `Hex.TSeriesBench.runLog` | `n ^ 2` |
| `Hex.TSeriesBench.runSqrt` | `n ^ 2 * (Nat.log2 (n + 1) + 1)` |
| `Hex.TSeriesBench.runCompHorner` | `n ^ 3` |
| `Hex.TSeriesBench.runCompBrentKung` | `n ^ 2 * Nat.sqrt n` |
| `Hex.TSeriesBench.runRevertNewton` | `n ^ 2 * Nat.sqrt n` |
| `Hex.TSeriesBench.runRevertLagrange` | `n ^ 3 * (Nat.log2 (n + 1) + 1)` |

The exponential and square-root expressions are wall-clock normalizations for
exact rational coefficient growth. Their textbook coefficient-operation bound
remains `O(n²)`: `exp x` produces factorial denominators with `Θ(n log n)`
bits, while `sqrt (1 + x)` produces growing exact binomial coefficients. The
adjacent registration comments distinguish these payload factors from the
algorithmic operation count.

The scheduled fixed registrations pair the Lean production route with
python-flint's `fmpq_series` wrapper at precisions `32..1024` for inverse,
`16..256` for exponential, logarithm, and square root, and `8..128` for
composition and reversion. Each arm uses five measured repeats, a 0.2 s
inner-batch floor, and a pinned `expectedHash`; the FLINT arm also warms and
reuses one persistent JSON-line subprocess per child. A separate fixed target
measures that protocol's steady-state framing overhead.

## Verdicts

The scientific parametric command was `lake exe hextruncatedseries_bench run
<all eleven parametric target names> --export-file <P>`. Inputs are generated
deterministically by the named `prep` function; the full parameter schedule is
recorded in P. Every registration returned `consistent with declared
complexity`:

| target | ladder | cMin | cMax | β | top-rung median |
|---|---:|---:|---:|---:|---:|
| `runMulInt` | 8–4096 | 6.159 | 7.302 | -0.028 | 103.337 ms |
| `runMulRat` | 8–4096 | 102.981 | 107.602 | -0.002 | 1.728 s |
| `runInverseNewton` | 8–4096 | 244.321 | 289.407 | -0.024 | 4.266 s |
| `runInverseRecurrence` | 8–4096 | 88.752 | 93.503 | -0.006 | 1.489 s |
| `runExp` | 8–1024 | 24.861 | 46.710 | +0.025 | 5.926 s |
| `runLog` | 8–1024 | 351.284 | 448.026 | -0.059 | 368.348 ms |
| `runSqrt` | 8–1024 | 165.891 | 176.718 | +0.003 | 1.985 s |
| `runCompHorner` | 8–512 | 103.305 | 119.439 | +0.027 | 16.031 s |
| `runCompBrentKung` | 8–512 | 224.831 | 282.773 | -0.052 | 1.348 s |
| `runRevertNewton` | 8–512 | 902.833 | 1068.028 | +0.028 | 6.159 s |
| `runRevertLagrange` | 8–512 | 22.802 | 26.226 | +0.007 | 33.191 s |

The three internal commands were `lake exe hextruncatedseries_bench compare
A B --export-file <I|C|R>`. Each reported agreement on every common parameter.
The measured first/second timing ratios were:

| comparison | ratios by precision |
|---|---|
| Newton inverse / recurrence | 8: 3.718×; 16: 3.357×; 32: 3.195×; 64: 2.924×; 128: 2.840×; 256: 2.836×; 512: 2.923×; 1024: 2.748×; 2048: 2.693×; 4096: 2.739× |
| Brent–Kung / Horner | 8: 0.922×; 16: 0.689×; 32: 0.424×; 64: 0.259×; 128: 0.196×; 256: 0.126×; 512: 0.084× |
| Newton reversion / Lagrange | 8: 2.763×; 16: 1.815×; 32: 1.152×; 64: 0.648×; 128: 0.423×; 256: 0.269×; 512: 0.186× |

Newton inversion stays below the required 4× recurrence bound at every rung.
The Brent–Kung/Horner ratio improves strictly across the complete ladder and
Brent–Kung wins at its top. Newton reversion crosses the Lagrange baseline
between 32 and 64 and widens its win thereafter.

`HEX_FLINT_BENCH_PYTHON=/tmp/hex-series-phase4-venv/bin/python lake exe
hextruncatedseries_bench verify` passed all 74 registrations. The fixed medians
and hash checks are reported with their paired ratios below; every repeat hash
agreed and every observed hash matched its pinned expected value.

## Comparator ratios

The sole declared comparator is FLINT fmpq_poly truncated series routines via python-flint,
classified `informational`. F used python-flint `0.9.0` under
Python `3.14.6` and the command
`HEX_FLINT_BENCH_PYTHON=/tmp/hex-series-phase4-venv/bin/python lake exe
hextruncatedseries_bench run --tag flint-series --export-file <F>`.

The persistent protocol overhead target measured 7.688 µs per call (median of
five; observed and expected hash `0x0`). “Raw” below is Lean median divided by
FLINT median. “Adjusted” subtracts 7.688 µs from the FLINT median first. All
rungs are eligible: overhead is at most 42.97% of FLINT wall time, and every
per-call time is below the 1 s soft ceiling. Adjusted values are shown at every
rung for a uniform table, including where overhead is already below 5%.

| family | n | Lean median | FLINT median | raw Hex/FLINT | adjusted Hex/FLINT | overhead / FLINT | output hash |
|---|---:|---:|---:|---:|---:|---:|---|
| inverse | 32 | 0.297 ms | 0.0346 ms | 8.588× | 11.043× | 22.23% | match |
| inverse | 64 | 1.107 ms | 0.0575 ms | 19.258× | 22.232× | 13.37% | match |
| inverse | 128 | 4.248 ms | 0.1030 ms | 41.259× | 44.589× | 7.47% | match |
| inverse | 256 | 16.507 ms | 0.1905 ms | 86.661× | 90.306× | 4.04% | match |
| inverse | 512 | 65.741 ms | 0.3773 ms | 174.246× | 177.870× | 2.04% | match |
| inverse | 1024 | 258.766 ms | 0.7418 ms | 348.816× | 352.469× | 1.04% | match |
| exp | 16 | 0.255 ms | 0.0247 ms | 10.322× | 14.994× | 31.16% | match |
| exp | 32 | 1.059 ms | 0.0554 ms | 19.126× | 22.210× | 13.88% | match |
| exp | 64 | 5.252 ms | 0.2986 ms | 17.592× | 18.057× | 2.57% | match |
| exp | 128 | 26.142 ms | 1.723 ms | 15.175× | 15.243× | 0.45% | match |
| exp | 256 | 134.422 ms | 9.412 ms | 14.282× | 14.294× | 0.08% | match |
| log | 16 | 0.114 ms | 0.0261 ms | 4.382× | 6.210× | 29.43% | match |
| log | 32 | 0.415 ms | 0.0394 ms | 10.530× | 13.083× | 19.51% | match |
| log | 64 | 1.556 ms | 0.0738 ms | 21.092× | 23.546× | 10.42% | match |
| log | 128 | 5.990 ms | 0.1378 ms | 43.462× | 46.029× | 5.58% | match |
| log | 256 | 23.308 ms | 0.2649 ms | 87.985× | 90.615× | 2.90% | match |
| sqrt | 16 | 0.210 ms | 0.0263 ms | 7.995× | 11.306× | 29.29% | match |
| sqrt | 32 | 1.014 ms | 0.0465 ms | 21.795× | 26.108× | 16.52% | match |
| sqrt | 64 | 4.955 ms | 0.1786 ms | 27.741× | 28.989× | 4.30% | match |
| sqrt | 128 | 23.063 ms | 1.052 ms | 21.928× | 22.089× | 0.73% | match |
| sqrt | 256 | 99.574 ms | 5.364 ms | 18.564× | 18.591× | 0.14% | match |
| composition | 8 | 0.0612 ms | 0.0221 ms | 2.766× | 4.237× | 34.73% | match |
| composition | 16 | 0.272 ms | 0.0318 ms | 8.568× | 11.302× | 24.19% | match |
| composition | 32 | 1.460 ms | 0.0515 ms | 28.349× | 33.323× | 14.93% | match |
| composition | 64 | 7.415 ms | 0.0996 ms | 74.477× | 80.709× | 7.72% | match |
| composition | 128 | 44.909 ms | 0.2608 ms | 172.217× | 177.448× | 2.95% | match |
| reversion | 8 | 0.229 ms | 0.0179 ms | 12.819× | 22.479× | 42.97% | match |
| reversion | 16 | 0.970 ms | 0.0249 ms | 38.944× | 56.323× | 30.86% | match |
| reversion | 32 | 5.185 ms | 0.0433 ms | 119.837× | 145.735× | 17.77% | match |
| reversion | 64 | 29.942 ms | 0.1516 ms | 197.457× | 208.003× | 5.07% | match |
| reversion | 128 | 184.880 ms | 0.8769 ms | 210.836× | 212.701× | 0.88% | match |

The exp ratio settles from its startup-affected bottom rungs toward about 14×;
sqrt peaks at 64 and declines toward 19×. Inverse, log, and composition show a
clear widening gap, while reversion approaches roughly 211× over its last two
rungs. This divergence is expected for the informational comparison: FLINT
uses coefficient-specific Karatsuba/Toom-Cook/FFT kernels while the generic
Lean multiplication contract is schoolbook. It does not contradict a gating
goal, and no external-comparator plot is required because only one comparator
is declared.

## Profile

One representative compiled case per declared family was profiled from the
same clean revision using samply `0.13.1` at 999 Hz and
lean-bench-samply commit
`9356baa2f5757ee40320a897bd284914d5bb9f5e`. The command form was:

```sh
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply \
  scripts/profile/run_profile.sh \
  ./.lake/build/bin/hextruncatedseries_bench \
  Hex.TSeriesBench.TARGET PARAM 5000000000
```

Raw filtered profiles, symbol sidecars, and diagnostics are developer-local
under `/tmp`, as required by `SPEC/profiling.md`. The profile hashes and filter
diagnostics are:

| family / target | profile path | profile SHA-256 | residual | timed | retained / rejected | off-thread | sensitivity |
|---|---|---|---:|---:|---:|---:|---|
| multiplication / `runMulRat 4096` | `/tmp/hex-profile-runMulRat-4096.json.gz` | `058f3902ee5dbc1cba8e89e63127d124b6d84ffc6eb192038323af7db5512636` | 0.539 ms | 5,197.693 ms | 5,183 / 11 | 0 | passed |
| inverse / `runInverseNewton 2048` | `/tmp/hex-profile-runInverseNewton-2048.json.gz` | `949ffce709d9ad045776df4d13ef3e5f7629f6474b46f6334beb6823f8f9dd90` | 0.875 ms | 5,176.234 ms | 5,146 / 11 | 0 | passed |
| exp-log / `runExp 512` | `/tmp/hex-profile-runExp-512.json.gz` | `aea30d1d8ba4d632985f861059281c9596ff7e5da421a6fb1bd00db0e5691b0f` | 0.395 ms | 4,040.377 ms | 3,996 / 14 | 0 | passed |
| sqrt / `runSqrt 1024` | `/tmp/hex-profile-runSqrt-1024.json.gz` | `2089b29f9d63d446d45fb0da8cc0414cf14d6bda2776d5b7b35b5d8ff145d251` | 0.532 ms | 6,024.805 ms | 5,994 / 7 | 0 | passed |
| composition / `runCompBrentKung 512` | `/tmp/hex-profile-runCompBrentKung-512.json.gz` | `408c15b0a7482abc499b941cb7adf3f4d30f99bf88c99f14bc43d5580c9cfeea` | 0.692 ms | 4,184.784 ms | 4,170 / 7 | 0 | passed |
| reversion / `runRevertNewton 512` | `/tmp/hex-profile-runRevertNewton-512.json.gz` | `cc454b23b95cd8768fd582ec118d595b1d3c94d56bd1564366307d75e1a58748` | 0.343 ms | 6,307.018 ms | 6,253 / 7 | 0 | passed |

Every filter reported `confidence: passed`. Leaf self-time, classified from
the symbol sidecars, was:

| family | own code | GMP | allocation/free | Lean runtime | other |
|---|---:|---:|---:|---:|---:|
| multiplication | 1.29% | 43.30% | 36.10% | 8.06% | 11.25% |
| inverse | 2.16% | 40.38% | 36.36% | 7.93% | 13.18% |
| exp-log | 0.58% | 59.56% | 26.10% | 3.35% | 10.41% |
| sqrt | 0.47% | 42.64% | 45.16% | 4.49% | 7.24% |
| composition | 1.56% | 37.31% | 40.67% | 8.51% | 11.94% |
| reversion | 1.20% | 34.29% | 47.85% | 6.11% | 10.55% |

The inclusive stacks attribute the costs to the registered routes:

- multiplication: `runMulRat` covered 99.98% and `TSeries.mul` 99.96%;
- inverse: `invUpTo` covered 100.00%, `mulUpToImpl` 99.75%, and `invStep`
  50.17%;
- exp-log: `runExp`/`expUpTo` covered 90.47%, `mulUpToImpl` 89.99%,
  `expStep` 70.05%, `logUpTo` 69.94%, and `invUpTo` 40.04%;
- sqrt: `runSqrt`/`sqrtUpTo` covered 94.49%, `mulUpToImpl` 94.43%, and
  `sqrtStep` 66.02%;
- composition: `runCompBrentKung` covered 99.90%, `compBrentKungUpTo`
  99.88%, `mulUpToImpl` 95.97%, and `powerTable` 39.76%;
- reversion: `runRevertNewton`/`revUpTo` covered 98.80%, `revStep` 98.56%,
  `mulUpToImpl` 94.90%, `compBrentKungUpTo` 94.51%, and `powerTable` 57.56%.

Thus the dominant inclusive costs all map to a registered benchmark target.
The leaf distributions also make the principal constant-factor cost explicit:
exact rational normalization spends most samples in GMP limb arithmetic and
allocation rather than in an unregistered preparation or oracle path.

## Concerns

None.
