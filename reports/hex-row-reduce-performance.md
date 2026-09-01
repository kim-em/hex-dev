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
`eb27e8ef52ec63aa4678d608132aa6e1cd556f891ca75b917a886a69a7cfa1d5`).
It was recorded from pristine source commit
`42342c7bb2883e51fd2d74f7f0dcbdc31c345a27` on `chungus2`, an AMD EPYC 9455
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
| `runReduce` | `n ^ 3` | -0.005 | 426.632–433.170 | pass |
| `runRank` | `n ^ 3` | -0.009 | 426.197–435.077 | pass |
| `runSpanCoeffs` | `n ^ 3` | -0.050 | 436.135–475.459 | pass |
| `runSpanContains` | `n ^ 3` | -0.050 | 435.694–473.041 | pass |
| `runEchelonSpanCoeffs` | `n ^ 2` | -0.013 | 453.992–467.313 | pass |
| `runEchelonSpanContains` | `n ^ 2` | -0.010 | 454.556–469.030 | pass |
| `runEchelonCoeffs` | `n` | — | 69.429–70.545 | pass |
| `runFreeCols` | `n` | — | 11.782–12.122 | pass |
| `runNullspaceMatrix` | `n ^ 3` | — | 155.758–158.224 | pass |
| `runNullspace` | `n ^ 3` | -0.028 | 156.683–164.129 | pass |
| `runReducedMatrix` | `n ^ 2` | +0.002 | 14.849–15.172 | pass |
| `runReducedNullspace` | `n ^ 2` | — | 14.984–16.286 | pass |

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
protocol overhead (7.158 us median), which is subtracted in the adjusted
ratios.

| `n` | Lean rank median | FLINT median | FLINT minus overhead | raw Lean / FLINT | adjusted Lean / FLINT |
|---:|---:|---:|---:|---:|---:|
| 16 | 1.771 ms | 11.287 us | 4.129 us | 156.9× | 428.8× |
| 24 | 5.949 ms | 15.750 us | 8.592 us | 377.7× | 692.3× |
| 32 | 13.987 ms | 22.038 us | 14.880 us | 634.7× | 940.0× |
| 48 | 47.056 ms | 42.992 us | 35.834 us | 1094.5× | 1313.2× |
| 64 | 111.623 ms | 77.369 us | 70.211 us | 1442.7× | 1589.8× |

This comparison is informational rather than gating: FLINT executes optimized
C/GMP kernels behind a Python call, while Hex exercises the generic Lean
matrix and exact-rational stack. Rank is the only identical callable surface
in the named comparator. RREF and nullspace values remain correctness-oracle
surfaces, and the other eleven benchmark targets carry the exact absence tag
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

For `runReducedMatrix`, inclusive samples attribute 42.83% to matrix
materialization, 37.91% to `nullspaceMatrix`, 10.26% to row access, and 5.34%
to the once-prepared pivot lookup. Leaf attribution is 39.02% library code,
34.35% Lean runtime, 10.01% allocation/free, and 16.62% other. The committed
summary is
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
