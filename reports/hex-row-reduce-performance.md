# HexRowReduce Performance Report

`HexRowReduce` provides exact row reduction, rank, span membership and
coefficients, and nullspace construction over the `HexMatrix` dense core. Its
compiled implementation routes free-column construction through a proved
sorted complement merge and prepares the column-to-pivot lookup once before
materializing a nullspace basis.

## Bench targets

The Mathlib-free `hexrowreduce_bench` executable registers direct mode-1
targets for every advertised runtime surface. Preparation is outside the timed
region for targets whose names begin with `runEchelon` or `runReduced`. The
declared input families are `dense-rational-rref` and
`rank-deficient-rational-nullspace`.

| target | timed operation | family | declared model |
|---|---|---|---:|
| `runReduce` | public RREF | dense rational RREF | `n ^ 3` |
| `runRank` | public rank | dense rational RREF | `n ^ 3` |
| `runSpanCoeffs` | public span coefficients | dense rational RREF | `n ^ 3` |
| `runSpanContains` | public span membership | dense rational RREF | `n ^ 3` |
| `runEchelonSpanCoeffs` | prepared span coefficients | dense rational RREF | `n ^ 2` |
| `runEchelonSpanContains` | prepared span membership | dense rational RREF | `n ^ 2` |
| `runEchelonCoeffs` | prepared coefficient selection | rank-deficient rational nullspace | `n` |
| `runFreeCols` | prepared free-column list | rank-deficient rational nullspace | `n` |
| `runNullspaceMatrix` | public nullspace matrix | rank-deficient rational nullspace | `n ^ 3` |
| `runNullspace` | public nullspace vectors | rank-deficient rational nullspace | `n ^ 3` |
| `runReducedMatrix` | prepared nullspace matrix | rank-deficient rational nullspace | `n ^ 2` |
| `runReducedNullspace` | prepared nullspace vectors | rank-deficient rational nullspace | `n ^ 2` |

The scientific artifact is
`reports/bench-results/hex-row-reduce-phase4-scientific.json` (SHA-256
`ecc174e4ac710fa928f6e31464251ca5a0484d0ef3073992246af1f3e9a5e2f2`).
It was recorded from pristine source commit
`2471e6e6c81a370fdd218b97d296d9033683dd3b` on `chungus2`, an AMD EPYC 9455
host running Lean 4.34.0-rc2 on x86-64 Linux. The exact command was:

```sh
HEX_FLINT_BENCH_PYTHON=/tmp/hex9811-flint/bin/python \
  .lake/build/bin/hexrowreduce_bench run \
  --filter Hex.RowReduceBench.run \
  --export-file reports/bench-results/hex-row-reduce-phase4-scientific.json
```

## Verdicts

All twelve targets are consistent with their declared complexity at the
default 0.15 slope tolerance. An em dash means the harness had too few eligible
adjacent-rung ratios to fit a slope; its normalized-constant verdict still
passed.

| target | model | fitted slope | normalized constant range | verdict |
|---|---:|---:|---:|---|
| `runReduce` | `n ^ 3` | -0.009 | 422.967–429.558 | pass |
| `runRank` | `n ^ 3` | -0.008 | 421.775–427.618 | pass |
| `runSpanCoeffs` | `n ^ 3` | -0.052 | 426.709–465.353 | pass |
| `runSpanContains` | `n ^ 3` | -0.052 | 426.680–466.068 | pass |
| `runEchelonSpanCoeffs` | `n ^ 2` | -0.006 | 453.532–467.502 | pass |
| `runEchelonSpanContains` | `n ^ 2` | +0.093 | 458.100–731.123 | pass |
| `runEchelonCoeffs` | `n` | — | 69.614–70.129 | pass |
| `runFreeCols` | `n` | — | 11.586–11.974 | pass |
| `runNullspaceMatrix` | `n ^ 3` | -0.026 | 155.269–162.348 | pass |
| `runNullspace` | `n ^ 3` | -0.030 | 154.539–162.149 | pass |
| `runReducedMatrix` | `n ^ 2` | -0.013 | 14.534–14.915 | pass |
| `runReducedNullspace` | `n ^ 2` | — | 14.921–16.169 | pass |

The compiled benchmark list contains 12 parametric and 11 fixed targets. All
fixed repeats agreed and every expected result hash matched. The full verify
suite also passes with python-flint 0.9.0.

## Comparator ratios

The declared informational comparator is
**FLINT fmpq_mat.rref rank via python-flint**, using python-flint 0.9.0. The one
identical callable result is rank of the same dense rational `I + J` matrix:
Lean calls the public `rank` API and FLINT calls `fmpq_mat.rref()` and returns
only its integer rank. The FLINT driver caches input construction and leaves
the cached matrix unchanged. A fixed O(1) endpoint measures the Python
protocol overhead (7.080 us median), which is subtracted in the adjusted
ratios.

| `n` | Lean rank median | FLINT median | FLINT minus overhead | raw Lean / FLINT | adjusted Lean / FLINT |
|---:|---:|---:|---:|---:|---:|
| 16† | 1.747 ms | 11.194 us | 4.114 us | 156.0× | 424.6× |
| 24 | 5.902 ms | 15.691 us | 8.611 us | 376.1× | 685.4× |
| 32 | 13.883 ms | 21.960 us | 14.880 us | 632.2× | 933.0× |
| 48 | 46.549 ms | 42.745 us | 35.665 us | 1089.0× | 1305.2× |
| 64 | 110.591 ms | 74.703 us | 67.623 us | 1480.4× | 1635.4× |

† At `n = 16`, protocol overhead is 63% of the FLINT wall time, so that rung
is reported for completeness but excluded from the eligible comparator range.
From the eligible `n = 24` rung through `n = 64`, the adjusted ratio increases
monotonically from 685.4× to 1635.4×. The widening gap reflects the different
measured regimes on this ladder: Hex follows cubic elimination, while the
overhead-adjusted FLINT endpoint is still below its cubic asymptote.

This comparison is informational rather than gating: FLINT executes optimized
C/GMP kernels behind a Python call, while Hex exercises the generic Lean
matrix and exact-rational stack. The Hex rank arm also computes the row
transform maintained by its shared `rowReduce` implementation, whereas FLINT's
`rref()` omits that output, so the ratios overstate a like-for-like rank gap.
Rank is the only identical callable result in the named comparator. RREF and
nullspace values remain correctness-oracle surfaces, and the other eleven
benchmark targets carry the exact absence tag
`no-comparable-surface-in-named-comparator`.

## Profile

One representative target from each declared input family was sampled at
999 Hz with samply 0.13.1 and lean-bench-samply commit
`9356baa2f5757ee40320a897bd284914d5bb9f5e`. Both profiles were captured from
pristine commit `f9fadac0cc8adfc2f87c2817fc3bbff863aa8c1f`; raw filtered profiles
and symbol sidecars remain developer-local under `/tmp`.

| family / target | residual | timed | retained / rejected | off-thread | sensitivity |
|---|---:|---:|---:|---:|---|
| dense rational RREF / `runReduce 64` | 0.358 ms | 1,910.945 ms | 1,901 / 7 | 0 | pass |
| rank-deficient rational nullspace / `runReducedMatrix 768` | 0.495 ms | 1,179.958 ms | 1,179 / 174 | 0 | pass |

For `runReduce`, inclusive samples attribute 99.95% to `rowReduce`, 99.89% to
`rowReduceLoop`, and 98.74% to row addition. Leaf attribution is 40.14% GMP,
34.46% allocation/free, 23.57% Lean runtime, 1.16% library code, and 0.68%
other. The committed summary is
`reports/bench-results/hex-row-reduce-profile-dense-rref-f9fadac0c-chungus2.json`
(SHA-256
`fd722fdc6fd4e6914a0529fbc8353b99bec002fe26dc9a3dfa75092a3863ddfa`).

For `runReducedMatrix`, inclusive samples attribute 47.24% to the benchmark's
result-forcing `matrixChecksum`, 42.83% to matrix materialization, 37.91% to
`nullspaceMatrix`, 10.26% to row access, and 5.34% to the once-prepared pivot
lookup. Result forcing is therefore a comparable share of the timed target,
not preparation. The automatic leaf classifier assigns 39.02% to library
code, 34.35% to Lean runtime, 10.01% to allocation/free, and 16.62% to other;
the latter includes the explicitly identified core checksum leaves
`instHashableRat.hash` (8.48%) and `Array.ofFn.go` (1.95%). Including those
named core leaves gives explicit attribution for 93.81% of samples. The
committed summary is
`reports/bench-results/hex-row-reduce-profile-deficient-nullspace-f9fadac0c-chungus2.json`
(SHA-256
`5fd918be67df847920e5efb52d8693e4c013b7303bbed83bbf850cbcd236e583`).

The exact commands were:

```sh
LEAN_BENCH_SAMPLY_HOME=/tmp/hex9811-lean-bench-samply \
  scripts/profile/run_profile.sh .lake/build/bin/hexrowreduce_bench \
  Hex.RowReduceBench.runReduce 64 3000000000
LEAN_BENCH_SAMPLY_HOME=/tmp/hex9811-lean-bench-samply \
  scripts/profile/run_profile.sh .lake/build/bin/hexrowreduce_bench \
  Hex.RowReduceBench.runReducedMatrix 768 3000000000
python3 scripts/profile/summarize_profile.py \
  /tmp/hex-profile-runReduce-64.json.gz --thread hexrowreduce_bench
python3 scripts/profile/summarize_profile.py \
  /tmp/hex-profile-runReducedMatrix-768.json.gz --thread hexrowreduce_bench
```

## Concerns

None.
