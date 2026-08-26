# HexHermite Performance Report

## Bench targets

The compiled Mathlib-free driver is `bench/HexHermite/Bench.lean`. Its
parametric registrations cover every executable public route and every input
family declared for `HexHermite`:

| target | operation and controlled input | declared model |
|---|---|---|
| `runDense` | form-only HNF, random dense square | `n ^ 3 * Nat.log2 (n + 1)` |
| `runDeficient` | form-only HNF, square of rank `n / 2` | `n ^ 3 * Nat.log2 (n + 1)` |
| `runTall` | form-only HNF, redundant `4n × n` | `n ^ 3` |
| `runConjugate` | form-only HNF, bounded `L * U * D` chain conjugate | `n ^ 3` |
| `runProfile` | fraction-free rank profile, dense | `n ^ 3 * Nat.log2 (n + 1)` |
| `runRankDense` | HNF rank projection, dense | `n ^ 3 * Nat.log2 (n + 1)` |
| `runBasisDense` | canonical nonzero-row basis, dense | `n ^ 3 * Nat.log2 (n + 1)` |
| `runDataDense` | HNF plus left transform, dense | `n ^ 3 * Nat.log2 (n + 1)` |
| `runWithInvDense` | HNF, transform, and inverse, dense | `n ^ 3 * Nat.log2 (n + 1)` |
| `runCoeffsDense` | constructive membership coefficients, dense | `n ^ 3 * Nat.log2 (n + 1)` |
| `runContainsDense` | membership decision, dense | `n ^ 3 * Nat.log2 (n + 1)` |
| `runKernelDeficient` | integer kernel basis, rank deficient | `n ^ 3 * Nat.log2 (n + 1)` |
| `runPivotsDense` | pivot projection, dense | `n ^ 3 * Nat.log2 (n + 1)` |
| `runIndexDense` | full-rank lattice index, dense | `n ^ 3 * Nat.log2 (n + 1)` |
| `runShapePrepared` | entry-level HNF checker, bounded prepared form | `n ^ 3` |
| `runCertPrepared` | packed replay of a bounded nontrivial certificate | `n ^ 3` |

The adjacent derivations in the driver charge cubic matrix traversal and, for
the random dense and deficient families, the observed arbitrary-precision
operand factor. The chain-conjugate generator uses deterministic signed
unit-lower and unit-upper bidiagonal factors, so it is not an already-HNF
shortcut. Shape and certificate inputs are prepared outside the timed region;
both timed functions abort if the prepared witness is rejected. The SPEC keeps
the conservative unrestricted `O(n⁴)` HNF ceiling separately from these
controlled-family wall models.

Thirteen fixed registrations retain exact expected hashes for the small API
smoke surface. Their clean-tree medians and matching observed hashes are in the
committed fixed export:

| fixed target | median | observed hash | expected |
|---|---:|---|---|
| `runIsHNFForm` | 17.840 us | `0xb` | match |
| `runCert` | 68.733 us | `0xb` | match |
| `runRank` | 50.750 us | `0x8` | match |
| `runBasis` | 101.526 us | `0x4bd6c0414a37c54a` | match |
| `runPivots` | 101.640 us | `0x88b839d5137f8c3d` | match |
| `runIndex` | 151.485 us | `0x52738` | match |
| `runData` | 66.329 us | `0xd37fb7926b798a32` | match |
| `runWithInv` | 86.855 us | `0x91815657fb9e95e2` | match |
| `runCoeffs` | 71.929 us | `0x93d3a019b62bba94` | match |
| `runCoeffsMiss` | 1.167 us | `0xb` | match |
| `runContains` | 71.944 us | `0xb` | match |
| `runContainsMiss` | 1.136 us | `0xb` | match |
| `runKernelBasis` | 62.796 us | `0x781397e5d22ca373` | match |

The remaining fixed registrations are two external-driver overhead probes and
sixty Lean/FLINT/PARI comparator targets: five sizes for each of four families.
All 75 fixed registrations have agreeing repeated hashes and matching expected
hashes in
[`hex-hermite-phase4-comparators.json`](bench-results/hex-hermite-phase4-comparators.json).

## Verdicts

The definitive scientific run used clean source commit
`828e4c493e96c7d17727fa1441f65b52605f3532`, Lean 4.34.0-rc2,
LeanBench 0.1.0, warm-cache compiled execution, and three outer trials on
`chungus2` (Linux x86-64, AMD EPYC 9455 48-Core Processor, 96 logical CPUs):

```sh
lake exe hexhermite_bench run \
  Hex.HermiteBench.runDense Hex.HermiteBench.runDeficient \
  Hex.HermiteBench.runTall Hex.HermiteBench.runConjugate \
  Hex.HermiteBench.runProfile Hex.HermiteBench.runRankDense \
  Hex.HermiteBench.runBasisDense Hex.HermiteBench.runDataDense \
  Hex.HermiteBench.runWithInvDense Hex.HermiteBench.runCoeffsDense \
  Hex.HermiteBench.runContainsDense Hex.HermiteBench.runKernelDeficient \
  Hex.HermiteBench.runPivotsDense Hex.HermiteBench.runIndexDense \
  Hex.HermiteBench.runShapePrepared Hex.HermiteBench.runCertPrepared \
  --export-file reports/bench-results/hex-hermite-phase4-scientific.json
```

The committed export has SHA-256
`107d6d342ff733d87d803c50c0b4aa3af2f21780cc4175c157b8f616ba6b32a0`.
Every target is consistent with its adjacent declared model:

| target | measured ladder | fitted slope | verdict window | spawn floor |
|---|---|---:|---|---:|
| `runDense` | 16, 24, 32, 48, 64, 96, 128 | -0.061826 | `41.207666..50.661434` | 22.116 ms |
| `runDeficient` | 16, 24, 32, 48, 64, 96, 128 | +0.028496 | `24.357564..27.769387` | 23.124 ms |
| `runTall` | 8, 12, 16, 24, 32, 48, 64 | -0.141281 | `405.822353..517.353568` | 23.425 ms |
| `runConjugate` | 16, 24, 32, 48, 64, 96, 128 | -0.005172 | `57.334616..59.226764` | 23.468 ms |
| `runProfile` | 16, 24, 32, 48, 64, 96, 128 | +0.074902 | `11.222693..14.177129` | 23.104 ms |
| `runRankDense` | 16, 24, 32, 48, 64, 96, 128 | -0.065728 | `41.071732..50.626645` | 22.976 ms |
| `runBasisDense` | 16, 24, 32, 48, 64, 96, 128 | -0.062589 | `82.408311..101.619480` | 23.267 ms |
| `runDataDense` | 16, 24, 32, 48, 64, 96, 128 | -0.026982 | `88.164525..105.940564` | 25.570 ms |
| `runWithInvDense` | 16, 24, 32, 48, 64, 96, 128 | -0.046670 | `107.918543..131.623719` | 23.436 ms |
| `runCoeffsDense` | 16, 24, 32, 48, 64, 96, 128 | -0.029139 | `87.519394..104.594206` | 22.499 ms |
| `runContainsDense` | 16, 24, 32, 48, 64, 96, 128 | -0.023969 | `87.502838..105.034674` | 23.302 ms |
| `runKernelDeficient` | 16, 24, 32, 48, 64, 96, 128 | +0.016563 | `62.058346..68.338874` | 22.437 ms |
| `runPivotsDense` | 16, 24, 32, 48, 64, 96, 128 | -0.070859 | `81.405803..101.082065` | 22.208 ms |
| `runIndexDense` | 16, 24, 32, 48, 64, 96, 128 | -0.059057 | `124.110706..152.460134` | 22.387 ms |
| `runShapePrepared` | 16, 24, 32, 48, 64, 96, 128, 192, 256 | -0.081707 | `19.030184..23.300597` | 23.603 ms |
| `runCertPrepared` | 64, 96, 128, 192, 256, 384, 512 | -0.130394 | `19.806378..24.719477` | 24.014 ms |

Every rung cleared the signal-floor filter. The largest three-trial spread was
10.042% at `runShapePrepared 128`; the fitted verdict remains stable over nine
rungs. All trials, inclusion flags, constants, spreads, and environment data
are committed in
[`hex-hermite-phase4-scientific.json`](bench-results/hex-hermite-phase4-scientific.json).

Untimed coefficient-growth instrumentation independently asserts that its
final matrix equals public `Matrix.hnf` and was reproduced with:

```sh
lake exe hexhermite_bench growth conjugate 16 24 32 48 64 96 128
lake exe hexhermite_bench growth dense 8 12 16 20 24 32
lake exe hexhermite_bench growth deficient 8 12 16 20 24 32
```

The committed output has SHA-256
`9e4bfa91f8370f9de55f6aa06fbc82f7e7d43e2216cf8b11df3ba7ddb5addfd0`.
The conjugate peak/output widths are 6/5, 6/5, 6/6, 7/6, 8/7, 8/7,
and 9/8 bits. Dense widths grow from 30/17 at `n=8` to 249/126 at
`n=32`; deficient widths grow from 18/13 to 120/64. These curves explain the
extra controlled operand factor on the dense and deficient wall models while
the conjugate family stays word-scale. They do not trigger a separate
coefficient-control algorithm issue.

## Comparator ratios

The registry's informational comparators are
`FLINT fmpz_mat_hnf via python-flint` (python-flint 0.9.0 / FLINT 3.6.0) and
`PARI mathnf via cypari2` (cypari2 2.2.4 / PARI 2.17.3). The clean
fixed export used source commit
`566f8985f9e8c55e49bce5ade266f8f367eed979`; that commit differs from the
scientific source only by committing its raw evidence. Reproduce all fixed
rows with:

```sh
nix-shell -p python313Packages.cypari2 python313Packages.cysignals pari --run '
  export HEX_FLINT_BENCH_PYTHON=/tmp/hexsmith-py/bin/python
  export HEX_PARI_BENCH_PYTHON=/tmp/hexsmith-py/bin/python
  fixed=$(.lake/build/bin/hexhermite_bench list | awk '\''/\[fixed\]/ {print $1}'\'')
  .lake/build/bin/hexhermite_bench run $fixed \
    --export-file reports/bench-results/hex-hermite-phase4-comparators.json
'
```

The 75-target export has SHA-256
`9f075784323e43e4ee2b2f5ff0f7ca27e76fd04fb6501f9654fb285c998f7c23`.
Its FLINT no-work median is 7.180 us and PARI's is 7.047 us. Every external
median exceeds twice its own overhead, every median is below ten seconds, and
all three implementations agree on the canonical HNF hash at all twenty
family/size points. The comparison command used for every point was:

```sh
for family in Dense Deficient Tall Conjugate; do
  for n in 16 24 32 40 48; do
    lake exe hexhermite_bench compare \
      Hex.HermiteBench.runHex${family}${n} \
      Hex.HermiteBench.runFlint${family}${n} \
      Hex.HermiteBench.runPari${family}${n}
  done
done
```

Adjusted ratios subtract only the measured request/reply floor from the
external time. Serialization and external matrix construction remain charged.

### Random dense Hermite

| n | Hex | FLINT | PARI | canonical hash | FLINT raw / adjusted | PARI raw / adjusted |
|---:|---:|---:|---:|---|---:|---:|
| 16 | 710.153 us | 121.410 us | 343.492 us | `0xd4c4d30cf11e3902` | 0.171x / 0.161x | 0.484x / 0.474x |
| 24 | 2.752 ms | 344.984 us | 877.531 us | `0xc2db6d9cd48562cf` | 0.125x / 0.123x | 0.319x / 0.316x |
| 32 | 7.146 ms | 752.846 us | 1.828 ms | `0x7dea452eb86f21c4` | 0.105x / 0.104x | 0.256x / 0.255x |
| 40 | 15.406 ms | 2.351 ms | 3.311 ms | `0x3e6a06331c9a70f5` | 0.153x / 0.152x | 0.215x / 0.214x |
| 48 | 27.853 ms | 2.858 ms | 4.859 ms | `0xf0b970d34f3479cf` | 0.103x / 0.102x | 0.174x / 0.174x |

Across the ladder, both external/Hex ratios decline overall (with a FLINT
threshold bump at `n=40`), so Hex loses relative ground as dense size grows.

![Random dense comparator runtimes](figures/hex-hermite-comparator-random-dense-hermite.svg)

### Rank-deficient Hermite

| n | Hex | FLINT | PARI | canonical hash | FLINT raw / adjusted | PARI raw / adjusted |
|---:|---:|---:|---:|---|---:|---:|
| 16 | 300.846 us | 117.399 us | 310.498 us | `0x8c3b42aee1b184e` | 0.390x / 0.366x | 1.032x / 1.009x |
| 24 | 1.460 ms | 304.681 us | 875.878 us | `0x9a533e7da7244459` | 0.209x / 0.204x | 0.600x / 0.595x |
| 32 | 4.083 ms | 1.173 ms | 1.787 ms | `0xe5df8cb1544b5979` | 0.287x / 0.285x | 0.438x / 0.436x |
| 40 | 8.640 ms | 2.600 ms | 5.244 ms | `0x705d86c1ef31d9c9` | 0.301x / 0.300x | 0.607x / 0.606x |
| 48 | 14.790 ms | 4.645 ms | 5.919 ms | `0x98d873e64dfda3bc` | 0.314x / 0.314x | 0.400x / 0.400x |

The deficient ratios are nonmonotone after the initial drop: FLINT settles in
the 0.204x--0.314x adjusted band, while PARI spans 0.400x--0.606x after
`n=16`. Five rungs support no stronger crossover claim.

![Rank-deficient comparator runtimes](figures/hex-hermite-comparator-rank-deficient-hermite.svg)

### Tall Hermite

| n | Hex | FLINT | PARI | canonical hash | FLINT raw / adjusted | PARI raw / adjusted |
|---:|---:|---:|---:|---|---:|---:|
| 16 | 1.995 ms | 395.436 us | 963.779 us | `0x8194afcd561bfd53` | 0.198x / 0.195x | 0.483x / 0.480x |
| 24 | 6.222 ms | 912.588 us | 4.110 ms | `0x720fca5c6fa3aec1` | 0.147x / 0.146x | 0.661x / 0.659x |
| 32 | 14.100 ms | 1.794 ms | 4.348 ms | `0x418e1a4c9e9d84b3` | 0.127x / 0.127x | 0.308x / 0.308x |
| 40 | 26.878 ms | 5.897 ms | 6.957 ms | `0x39dab28adc1593b5` | 0.219x / 0.219x | 0.259x / 0.259x |
| 48 | 45.818 ms | 10.209 ms | 10.365 ms | `0xb51a4d975bdc6feb` | 0.223x / 0.223x | 0.226x / 0.226x |

FLINT's ratio bottoms at `n=32` and then returns to 0.223x; PARI's adjusted
ratio falls steadily from its `n=24` peak to 0.226x. Hex remains slower on all
five tall points.

![Tall comparator runtimes](figures/hex-hermite-comparator-tall-hermite.svg)

### Unimodular conjugate

| n | Hex | FLINT | PARI | canonical hash | FLINT raw / adjusted | PARI raw / adjusted |
|---:|---:|---:|---:|---|---:|---:|
| 16 | 255.541 us | 95.897 us | 224.122 us | `0x1b4006b1f4d4df66` | 0.375x / 0.347x | 0.877x / 0.849x |
| 24 | 1.000 ms | 202.065 us | 475.667 us | `0xe47f13aca06b7628` | 0.202x / 0.195x | 0.476x / 0.469x |
| 32 | 2.246 ms | 366.653 us | 937.505 us | `0x531c1c24c585ac12` | 0.163x / 0.160x | 0.417x / 0.414x |
| 40 | 4.333 ms | 3.840 ms | 1.521 ms | `0xfc1deb59344974c8` | 0.886x / 0.885x | 0.351x / 0.349x |
| 48 | 7.378 ms | 10.785 ms | 2.194 ms | `0x501203bf9b14db75` | 1.462x / 1.461x | 0.297x / 0.296x |

PARI's ratio declines across the ladder. FLINT shows a clear threshold change
between 32 and 40 and is slower than Hex at 48; the raw repeated medians and
matching hashes make this an observed comparator transition, not a claimed
general crossover.

![Unimodular-conjugate comparator runtimes](figures/hex-hermite-comparator-unimodular-conjugate.svg)

Regenerate all four figures with:

```sh
for family in random-dense-hermite rank-deficient-hermite tall-hermite \
    unimodular-conjugate; do
  python3 scripts/plots/hex-hermite-comparator.py --family "$family"
done
```

## Profile

Every declared family was profiled from clean commit
`c67c89035f8262f7303c89a464403e870297c980`, which differs from the timed
source only by committed evidence. Samply 0.13.1 ran at 999 Hz with filtered
timed regions:

```sh
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply \
  scripts/profile/run_profile.sh .lake/build/bin/hexhermite_bench \
  Hex.HermiteBench.runDense 128 5000000000
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply \
  scripts/profile/run_profile.sh .lake/build/bin/hexhermite_bench \
  Hex.HermiteBench.runDeficient 128 5000000000
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply \
  scripts/profile/run_profile.sh .lake/build/bin/hexhermite_bench \
  Hex.HermiteBench.runTall 64 5000000000
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply \
  scripts/profile/run_profile.sh .lake/build/bin/hexhermite_bench \
  Hex.HermiteBench.runConjugate 128 5000000000
```

Raw filtered profiles remain developer-local under `/tmp`, as required by
`SPEC/profiling.md`. Each summary used
`scripts/profile/summarize_profile.py --thread hexhermite_bench`; calibration,
confidence, and ±5 ms sensitivity checks all passed.

### Random dense Hermite

The profile retained 5,439 samples and rejected 8. Leaf cost was allocation
49.88%, GMP 21.82%, Lean runtime 19.97%, Hex own code 8.22%, and other 0.11%
(99.89% classified).

| inclusive Hex function | share |
|---|---:|
| `Hex.HermiteBench.runDense` | 96.75% |
| `Hex.Matrix.Hermite.checkedRun` | 96.65% |
| `Hex.Matrix.Hermite.principalCore` | 60.73% |
| `Hex.Matrix.Hermite.clearPrior` | 48.61% |
| `Hex.Matrix.Hermite.normalizeRow` | 35.23% |
| `Hex.Matrix.Hermite.reduceStep` | 33.72% |

Principal reduction and immutable row updates dominate; growing integer
coefficients explain the GMP share. Calibration residual was 0.492 ms and
total timed work was 5,496.5 ms.

### Rank-deficient Hermite

The profile retained 3,360 samples and rejected 9. Leaf cost was allocation
58.84%, GMP 17.68%, Lean runtime 16.19%, Hex own code 7.05%, and other 0.24%
(99.76% classified).

| inclusive Hex function | share |
|---|---:|
| `Hex.HermiteBench.runDeficient` | 98.60% |
| `Hex.Matrix.Hermite.checkedRun` | 98.24% |
| `Hex.Matrix.Hermite.principalCore` | 63.87% |
| `Hex.Matrix.Hermite.clearPrior` | 56.58% |
| `Hex.Matrix.Hermite.gcdStep` | 42.50% |
| `Hex.Matrix.Hermite.combineRows` | 41.96% |

Dependent-row reconstruction through `gcdStep` and `combineRows` dominates the
registered HNF route. Calibration residual was 0.928 ms and total timed work
was 3,380.0 ms.

### Tall Hermite

The profile retained 3,461 samples and rejected 8. Leaf cost was Lean runtime
61.14%, Hex own code 27.02%, allocation 11.73%, and other 0.12% (99.88%
classified); GMP did not register at the reporting precision.

| inclusive Hex function | share |
|---|---:|
| `Hex.HermiteBench.runTall` | 99.97% |
| `Hex.Matrix.Hermite.checkedRun` | 99.83% |
| `Hex.Matrix.Hermite.principalCore` | 73.74% |
| `Hex.Matrix.Hermite.clearPrior` | 73.04% |
| `Hex.Matrix.Hermite.normalizeRow` | 40.08% |
| `Hex.Matrix.Hermite.gcdStep` | 31.23% |

Clearing redundant rows over word-scale entries is dominated by Lean traversal
rather than big integers. Calibration residual was 0.847 ms and total timed
work was 3,469.8 ms.

### Unimodular conjugate

The profile retained 4,052 samples and rejected 17. Leaf cost was Lean runtime
53.53%, Hex own code 27.67%, allocation 11.53%, GMP 7.08%, and other 0.20%
(99.80% classified).

| inclusive Hex function | share |
|---|---:|
| `Hex.HermiteBench.runConjugate` | 99.85% |
| `Hex.Matrix.Hermite.checkedRun` | 99.70% |
| `Hex.Matrix.Hermite.profileStep` | 45.98% |
| `Hex.Matrix.ofFn` | 38.25% |
| `Hex.Matrix.Hermite.profileEliminate` | 31.00% |
| `Hex.Matrix.isHNFForm` | 20.71% |
| `Hex.Matrix.Hermite.principalCore` | 19.32% |

The fraction-free rank-profile stage is dominant, and the registered checked
HNF route explicitly charges its form validation. Calibration residual was
0.971 ms and total timed work was 4,079.2 ms.

`HexHermiteMathlib` declares `correspondence-only-layer` and names
`HexHermite` as its performance owner. It owns no independent runtime
computation, so it has no synthetic benchmark or separate report.

## Concerns

None.
