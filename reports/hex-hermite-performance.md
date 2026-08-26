# HexHermite Performance Report

## Bench targets

The compiled Mathlib-free driver is `bench/HexHermite/Bench.lean`. It registers
17 controlled parametric targets and 75 fixed targets (92 total). The adjacent
comments in the driver derive each model from the work performed inside the
timed function.

| target | operation and controlled input | declared model |
|---|---|---|
| `runDense` | form-only HNF, random dense square | `n ^ 3 * Nat.log2 (n + 1)` |
| `runDeficient` | form-only HNF, square of rank `n / 2` | `n ^ 3 * Nat.log2 (n + 1)` |
| `runTall` | form-only HNF, redundant `4n × n` | `n ^ 3` |
| `runConjugate` | form-only HNF, full triangular `L * U * D` | `n ^ 3 * Nat.log2 (n + 1)` |
| `runProfile` | fraction-free rank profile, dense | `n ^ 3 * Nat.log2 (n + 1)` |
| `runPrincipalDense` | prepared principal HNF phase, dense | `n ^ 3 * Nat.log2 (n + 1)` |
| `runRankDense` | HNF rank projection, dense | `n ^ 3 * Nat.log2 (n + 1)` |
| `runBasisDense` | canonical nonzero-row basis, dense | `n ^ 3 * Nat.log2 (n + 1)` |
| `runDataDense` | HNF plus left transform, dense | `n ^ 3 * Nat.log2 (n + 1)` |
| `runWithInvDense` | HNF, transform, and inverse, dense | `n ^ 3 * Nat.log2 (n + 1)` |
| `runCoeffsDense` | coefficients for a nonzero known member | `n ^ 3 * Nat.log2 (n + 1)` |
| `runContainsDense` | decision for a nonzero known member | `n ^ 3 * Nat.log2 (n + 1)` |
| `runKernelDeficient` | integer kernel basis, rank deficient | `n ^ 3 * Nat.log2 (n + 1)` |
| `runPivotsDense` | pivot projection, dense | `n ^ 3 * Nat.log2 (n + 1)` |
| `runIndexDense` | full-rank lattice index, dense | `n ^ 3 * Nat.log2 (n + 1)` |
| `runShapePrepared` | direct HNF predicate on a prepared form | `n ^ 2` |
| `runCertPrepared` | packed certificate replay | `n ^ 2 * Nat.log2 (n + 1)` |

The dense and deficient schedules make cubic matrix visits while measured
operand widths grow over their ladders. The tall family has fixed aspect ratio
and word-scale coefficients. The conjugate generator uses every entry of
deterministic unit-lower and unit-upper triangular factors, rather than a
bidiagonal shortcut, and the measured coefficient ladder supplies its explicit
logarithmic factor. `runShapePrepared` uses constant-time tuple entry access;
`runCertPrepared` charges packed-integer width. Prepared witnesses are checked
by build-time `#guard`s. A further build-time guard compares the isolated
principal result with public `hnf` on the same dense input.

`hnfBasis`, `kernelBasis`, `pivots`, and `latticeIndex` each project from one
shared HNF result. Their ladders therefore measure one form/transform run, not
the former hidden two- or three-run constants.

The thirteen small API fixed targets have the following medians in the
committed [fixed export](bench-results/hex-hermite-phase4-comparators.json):

| fixed target | median | observed hash | expected |
|---|---:|---|---|
| `runIsHNFForm` | 6.360 us | `0xb` | match |
| `runCert` | 57.134 us | `0xb` | match |
| `runRank` | 38.933 us | `0x8` | match |
| `runBasis` | 39.661 us | `0x4bd6c0414a37c54a` | match |
| `runPivots` | 39.287 us | `0x88b839d5137f8c3d` | match |
| `runIndex` | 39.183 us | `0x52738` | match |
| `runData` | 54.367 us | `0xd37fb7926b798a32` | match |
| `runWithInv` | 74.774 us | `0x91815657fb9e95e2` | match |
| `runCoeffs` | 59.693 us | `0x93d3a019b62bba94` | match |
| `runCoeffsMiss` | 1.067 us | `0xb` | match |
| `runContains` | 59.678 us | `0xb` | match |
| `runContainsMiss` | 1.082 us | `0xb` | match |
| `runKernelBasis` | 31.991 us | `0x781397e5d22ca373` | match |

The other 62 fixed registrations are two external-driver overhead probes and
60 Lean/FLINT/PARI comparator targets. All 75 fixed registrations have
agreeing repeat hashes and matching expected hashes.

## Verdicts

The definitive run used clean source commit
`cdfc17b733b3f51bf06ef16eb2d4738caeca4b72`, Lean 4.34.0-rc2,
LeanBench 0.1.0, warm-cache compiled execution, and three outer trials on
`chungus2` (Linux x86-64, AMD EPYC 9455 48-Core Processor, 96 logical CPUs):

```sh
.lake/build/bin/hexhermite_bench run \
  Hex.HermiteBench.runDense Hex.HermiteBench.runDeficient \
  Hex.HermiteBench.runTall Hex.HermiteBench.runConjugate \
  Hex.HermiteBench.runProfile Hex.HermiteBench.runPrincipalDense \
  Hex.HermiteBench.runRankDense Hex.HermiteBench.runBasisDense \
  Hex.HermiteBench.runDataDense Hex.HermiteBench.runWithInvDense \
  Hex.HermiteBench.runCoeffsDense Hex.HermiteBench.runContainsDense \
  Hex.HermiteBench.runKernelDeficient Hex.HermiteBench.runPivotsDense \
  Hex.HermiteBench.runIndexDense Hex.HermiteBench.runShapePrepared \
  Hex.HermiteBench.runCertPrepared \
  --export-file reports/bench-results/hex-hermite-phase4-scientific.json
```

The committed [scientific export](bench-results/hex-hermite-phase4-scientific.json)
has SHA-256
`cc564cddf7b2556940b12d8bd447d627499b09d7716df6bc9093be8e093a0835`.
Every target is consistent with its declared model:

| target | measured ladder | fitted slope | verdict window | spawn floor |
|---|---|---:|---|---:|
| `runDense` | 16, 24, 32, 48, 64, 96, 128 | -0.041707 | `38.203267..46.409749` | 22.546 ms |
| `runDeficient` | 16, 24, 32, 48, 64, 96, 128 | +0.051904 | `22.828678..26.503867` | 23.219 ms |
| `runTall` | 8, 12, 16, 24, 32, 48, 64 | -0.127789 | `363.827073..435.924734` | 23.423 ms |
| `runConjugate` | 16, 24, 32, 48, 64, 96, 128 | +0.054221 | `16.280815..19.657609` | 22.553 ms |
| `runProfile` | 16, 24, 32, 48, 64, 96, 128 | +0.069661 | `11.265390..14.073204` | 22.885 ms |
| `runPrincipalDense` | 16, 24, 32, 48, 64, 96, 128 | -0.060431 | `25.656904..32.764767` | 23.634 ms |
| `runRankDense` | 16, 24, 32, 48, 64, 96, 128 | -0.033928 | `38.396382..46.396249` | 22.853 ms |
| `runBasisDense` | 16, 24, 32, 48, 64, 96, 128 | -0.035505 | `38.239014..46.637288` | 22.539 ms |
| `runDataDense` | 16, 24, 32, 48, 64, 96, 128 | -0.016642 | `84.133045..100.916917` | 35.501 ms |
| `runWithInvDense` | 16, 24, 32, 48, 64, 96, 128 | -0.030895 | `105.435018..127.149182` | 37.123 ms |
| `runCoeffsDense` | 16, 24, 32, 48, 64, 96, 128 | -0.016024 | `83.699194..101.315753` | 23.492 ms |
| `runContainsDense` | 16, 24, 32, 48, 64, 96, 128 | -0.003052 | `83.757245..100.977523` | 22.530 ms |
| `runKernelDeficient` | 16, 24, 32, 48, 64, 96, 128 | +0.016276 | `36.189203..39.717959` | 29.551 ms |
| `runPivotsDense` | 16, 24, 32, 48, 64, 96, 128 | -0.034486 | `38.330193..46.806665` | 41.775 ms |
| `runIndexDense` | 16, 24, 32, 48, 64, 96, 128 | -0.036557 | `38.221382..46.734275` | 22.577 ms |
| `runShapePrepared` | 16, 24, 32, 48, 64, 96, 128, 192, 256 | -0.055156 | `59.789058..67.991759` | 42.010 ms |
| `runCertPrepared` | 64, 96, 128, 192, 256, 384, 512 | -0.073983 | `75.467502..91.381558` | 22.669 ms |

The tall verdict excludes the two startup rungs (8 and 12) under its declared
30% warmup fraction while retaining all seven raw rungs. Other fits exclude
only their first rung. Two kernel trials at 48 and 64 contain visible host
jitter (74.896% and 70.395% spreads); the three-trial medians, adjacent rungs,
and fitted verdict remain consistent. The raw export preserves every trial,
fit-inclusion flag, constant, spread, and environment field.

The untimed growth runner scans the working matrix after every elementary
update and asserts that its final matrix equals public `Matrix.hnf`. Reproduce
the full timed-family ranges with:

```sh
lake exe hexhermite_bench growth conjugate 16 24 32 48 64 96 128
lake exe hexhermite_bench growth dense 8 12 16 24 32 48 64 96 128
lake exe hexhermite_bench growth deficient 8 12 16 24 32 48 64 96 128
lake exe hexhermite_bench growth tall 8 12 16 24 32 48 64
```

The committed [growth transcript](bench-results/hex-hermite-phase4-growth.txt)
records source commit `136980ce850c3c89b7ed90902b07eb1318336dae`, Lean and
LeanBench versions, host, OS, family, dimension, peak width, and output width;
its SHA-256 is
`e567ae1b90713b599db0a3330b99605e404b40f8c65332f3026bb5d9a30a625b`.
Dense grows from 30/17 bits at `n=8` to 1375/691 at `n=128`, deficient
from 18/13 to 640/323, and tall from 6/4 to 12/7. Conjugate grows from
12/5 at `n=16` to 70/8 at `n=128`: peak width diverges materially from
output width, and its wall ladder follows the declared extra operand factor.
This satisfies the SPEC's predeclared trigger; issue #9689 records the bounded
Havas-Majewski-Matthews evaluation follow-up without adding that algorithm to
this release unit.

## Comparator ratios

The informational comparators are `FLINT fmpz_mat_hnf via python-flint`
(python-flint 0.9.0 / FLINT 3.6.0) and `PARI mathnf via cypari2`
(cypari2 2.2.4 / PARI 2.17.3). The clean fixed run used source commit
`8692efcfd` on the same host and toolchain:

```sh
nix-shell -p python313Packages.cypari2 python313Packages.cysignals pari --run '
  export HEX_FLINT_BENCH_PYTHON=/tmp/hexsmith-py/bin/python
  export HEX_PARI_BENCH_PYTHON=/tmp/hexsmith-py/bin/python
  fixed=$(.lake/build/bin/hexhermite_bench list | awk '\''/\[fixed\]/ {print $1}'\'')
  .lake/build/bin/hexhermite_bench run $fixed \
    --export-file reports/bench-results/hex-hermite-phase4-comparators.json
'
```

The [75-target export](bench-results/hex-hermite-phase4-comparators.json) has
SHA-256
`4268fe3f8c3e15ff168c9298a7bc0f0a8a4d7c31aa5dca5a10f5542652e23478`.
FLINT's no-work median is 7.062 us and PARI's is 6.962 us. Every external
median exceeds twice its own overhead, is below ten seconds, and agrees with
Lean's canonical HNF hash at all 20 common-domain points. Adjusted ratios
subtract only the matching external request/reply floor; serialization and
external matrix construction remain charged.

### Random dense Hermite

| n | Hex | FLINT | PARI | canonical hash | FLINT raw / adjusted | PARI raw / adjusted |
|---:|---:|---:|---:|---|---:|---:|
| 16 | 606.148 us | 122.447 us | 344.227 us | `0xd4c4d30cf11e3902` | 0.202x / 0.190x | 0.568x / 0.556x |
| 24 | 2.435 ms | 344.055 us | 862.298 us | `0xc2db6d9cd48562cf` | 0.141x / 0.138x | 0.354x / 0.351x |
| 32 | 6.520 ms | 743.917 us | 1.806 ms | `0x7dea452eb86f21c4` | 0.114x / 0.113x | 0.277x / 0.276x |
| 40 | 14.119 ms | 2.359 ms | 3.323 ms | `0x3e6a06331c9a70f5` | 0.167x / 0.167x | 0.235x / 0.235x |
| 48 | 25.594 ms | 2.880 ms | 4.886 ms | `0xf0b970d34f3479cf` | 0.113x / 0.112x | 0.191x / 0.191x |

Both external/Hex ratios decline overall; the FLINT threshold bump at 40 does
not support a crossover claim.

![Random dense comparator runtimes](figures/hex-hermite-comparator-random-dense-hermite.svg)

### Rank-deficient Hermite

| n | Hex | FLINT | PARI | canonical hash | FLINT raw / adjusted | PARI raw / adjusted |
|---:|---:|---:|---:|---|---:|---:|
| 16 | 267.639 us | 116.816 us | 309.591 us | `0x8c3b42aee1b184e` | 0.436x / 0.410x | 1.157x / 1.131x |
| 24 | 1.360 ms | 302.433 us | 872.873 us | `0x9a533e7da7244459` | 0.222x / 0.217x | 0.642x / 0.637x |
| 32 | 3.828 ms | 1.178 ms | 1.801 ms | `0xe5df8cb1544b5979` | 0.308x / 0.306x | 0.470x / 0.469x |
| 40 | 8.169 ms | 2.589 ms | 5.113 ms | `0x705d86c1ef31d9c9` | 0.317x / 0.316x | 0.626x / 0.625x |
| 48 | 13.989 ms | 4.660 ms | 5.876 ms | `0x98d873e64dfda3bc` | 0.333x / 0.333x | 0.420x / 0.420x |

The deficient ratios are nonmonotone after the initial drop, so five rungs
support no stronger crossover statement.

![Rank-deficient comparator runtimes](figures/hex-hermite-comparator-rank-deficient-hermite.svg)

### Tall Hermite

| n | Hex | FLINT | PARI | canonical hash | FLINT raw / adjusted | PARI raw / adjusted |
|---:|---:|---:|---:|---|---:|---:|
| 16 | 1.779 ms | 395.899 us | 1.006 ms | `0x8194afcd561bfd53` | 0.223x / 0.219x | 0.565x / 0.561x |
| 24 | 5.619 ms | 914.620 us | 4.333 ms | `0x720fca5c6fa3aec1` | 0.163x / 0.162x | 0.771x / 0.770x |
| 32 | 12.718 ms | 1.768 ms | 4.334 ms | `0x418e1a4c9e9d84b3` | 0.139x / 0.138x | 0.341x / 0.340x |
| 40 | 23.928 ms | 5.858 ms | 7.024 ms | `0x39dab28adc1593b5` | 0.245x / 0.245x | 0.294x / 0.293x |
| 48 | 40.739 ms | 10.243 ms | 10.357 ms | `0xb51a4d975bdc6feb` | 0.251x / 0.251x | 0.254x / 0.254x |

Hex remains slower at all five tall points. The DKT/modular question therefore
remains an algorithm-design question, not a reason to claim a measured
crossover for the current implementation.

![Tall comparator runtimes](figures/hex-hermite-comparator-tall-hermite.svg)

### Unimodular conjugate

| n | Hex | FLINT | PARI | canonical hash | FLINT raw / adjusted | PARI raw / adjusted |
|---:|---:|---:|---:|---|---:|---:|
| 16 | 285.768 us | 103.828 us | 308.267 us | `0x1b4006b1f4d4df66` | 0.363x / 0.339x | 1.079x / 1.054x |
| 24 | 1.382 ms | 229.841 us | 775.544 us | `0xe47f13aca06b7628` | 0.166x / 0.161x | 0.561x / 0.556x |
| 32 | 3.415 ms | 446.644 us | 1.643 ms | `0x531c1c24c585ac12` | 0.131x / 0.129x | 0.481x / 0.479x |
| 40 | 6.909 ms | 785.524 us | 2.796 ms | `0xfc1deb59344974c8` | 0.114x / 0.113x | 0.405x / 0.404x |
| 48 | 12.449 ms | 7.183 ms | 4.267 ms | `0x501203bf9b14db75` | 0.577x / 0.576x | 0.343x / 0.342x |

FLINT changes threshold between 40 and 48 but remains faster at every point;
PARI's ratio declines across the ladder. These are informational observations,
not thresholds required by the registry.

![Unimodular-conjugate comparator runtimes](figures/hex-hermite-comparator-unimodular-conjugate.svg)

Regenerate the figures with:

```sh
for family in random-dense-hermite rank-deficient-hermite tall-hermite \
    unimodular-conjugate; do
  python3 scripts/plots/hex-hermite-comparator.py --family "$family"
done
```

## Profile

Samply 0.13.1 profiled clean commit `11d29fee274c0e27390d3ffd098515a0c9505069`
at 999 Hz on the same `chungus2` hardware, Lean 4.34.0-rc2, and LeanBench
0.1.0. Inputs are deterministic: dense salt 5, deficient salt 17, full
triangular salts 41/43, and the fixed tall construction in the bench source.
No runtime oracle participates in any profiled Lean route.

```sh
export LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply
scripts/profile/run_profile.sh .lake/build/bin/hexhermite_bench \
  Hex.HermiteBench.runDense 128 5000000000
scripts/profile/run_profile.sh .lake/build/bin/hexhermite_bench \
  Hex.HermiteBench.runDeficient 128 5000000000
scripts/profile/run_profile.sh .lake/build/bin/hexhermite_bench \
  Hex.HermiteBench.runTall 64 5000000000
scripts/profile/run_profile.sh .lake/build/bin/hexhermite_bench \
  Hex.HermiteBench.runConjugate 128 5000000000
scripts/profile/run_profile.sh .lake/build/bin/hexhermite_bench \
  Hex.HermiteBench.runPrincipalDense 128 5000000000
```

Raw filtered profiles remain developer-local under `/tmp` as required by
`SPEC/profiling.md`. Each summary used
`python3 scripts/profile/summarize_profile.py --thread hexhermite_bench`.
All five profiles passed calibration, confidence, and ±5 ms sensitivity.

| profile | retained / rejected samples | dominant inclusive registered/owned cost | leaf-cost summary |
|---|---:|---|---|
| dense 128 | 5,093 / 8 | `principalCore` 65.05% | allocation 53.43%, GMP 23.78%, runtime 16.24% |
| deficient 128 | 3,200 / 13 | `principalCore` 66.19% | allocation 61.31%, GMP 19.31%, runtime 14.00% |
| tall 64 | 3,182 / 14 | `principalCore` 82.68% | runtime 60.72%, own code 26.78%, allocation 12.38% |
| conjugate 128 | 4,883 / 40 | `runProfile` phase 60.31%; `principalCore` 36.13% | allocation 39.07%, runtime 25.60%, GMP 23.76% |
| principal 128 | 3,397 / 182 | `runPrincipalDense` / `principalCore` 96.47% | allocation 57.79%, GMP 18.10%, runtime 17.96% |

Thus every dominant separable phase is attributed to a registered target.
Dense/deficient/tall spend most time in principal reduction and immutable row
updates; conjugate shifts dominance to fraction-free profiling as its full
triangular factors condition the input. The dedicated principal profile links
that inclusive cost directly to `runPrincipalDense`.

`HexHermiteMathlib` declares `correspondence-only-layer` and names
`HexHermite` as its performance owner. It owns no independent runtime
computation and therefore has no synthetic benchmark or separate report.

## Concerns

None.
