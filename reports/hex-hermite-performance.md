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

The dense, deficient, and conjugate schedules make cubic matrix visits while
measured peak widths grow roughly linearly over their ladders. Their
`n³ log₂(n + 1)` normalizer is an empirically calibrated, slowly growing wall
surrogate over 16..128, not a bit-complexity consequence of that width curve.
The tall family has fixed aspect ratio and word-scale coefficients. The
conjugate generator uses every entry of deterministic unit-lower and unit-upper
triangular factors, rather than a bidiagonal shortcut. `runShapePrepared` uses
constant-time tuple entry access;
`runCertPrepared` uses a unit-bidiagonal transform, so its two packed product
checks have only two nonzero packed terms per row. Its `n² log n` model is a
calibrated surrogate for this bounded sparse-transform certificate family, not
for general `hnfCert` replay with a dense transform. Prepared witnesses are
checked by build-time `#guard`s. A further build-time guard compares the isolated
principal result with public `hnf` on the same dense input.

`hnfBasis`, `kernelBasis`, `pivots`, and `latticeIndex` each project from one
shared HNF result. Previously, form/transform computation occurred inside
entry-producing closures for basis and kernel extraction, causing a full run
per output entry; pivots and index separately repeated their form projections.
The new ladders measure one shared run followed by the advertised projection.

The thirteen small API fixed targets have the following medians in the
committed [fixed export](bench-results/hex-hermite-phase4-comparators.json):

| fixed target | median | observed hash | expected |
|---|---:|---|---|
| `runIsHNFForm` | 6.263 us | `0xb` | match |
| `runCert` | 57.625 us | `0xb` | match |
| `runRank` | 39.065 us | `0x8` | match |
| `runBasis` | 39.776 us | `0x4bd6c0414a37c54a` | match |
| `runPivots` | 38.765 us | `0x88b839d5137f8c3d` | match |
| `runIndex` | 39.114 us | `0x52738` | match |
| `runData` | 54.732 us | `0xd37fb7926b798a32` | match |
| `runWithInv` | 75.137 us | `0x91815657fb9e95e2` | match |
| `runCoeffs` | 59.593 us | `0x93d3a019b62bba94` | match |
| `runCoeffsMiss` | 1.081 us | `0xb` | match |
| `runContains` | 59.573 us | `0xb` | match |
| `runContainsMiss` | 1.090 us | `0xb` | match |
| `runKernelBasis` | 31.917 us | `0x781397e5d22ca373` | match |

The other 62 fixed registrations are two external-driver overhead probes and
60 Lean/FLINT/PARI comparator targets. All 75 fixed registrations have
agreeing repeat hashes and matching expected hashes.

## Verdicts

The definitive run used clean source commit
`fb8595cc1e0eaa74f5b9f8760e25ba38ac02faf3` (content-identical rebased
commit `7218f3bbe8e4577e9d1a2b5f62452609982565ce`), Lean 4.34.0-rc2,
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
`26de21b7fd32e3e72f6812a535fc71aef81ede13d14465d7aaed582cee267724`.
Every target is consistent with its declared model:

| target | measured ladder | fitted slope | verdict window | spawn floor |
|---|---|---:|---|---:|
| `runDense` | 16, 24, 32, 48, 64, 96, 128 | -0.034478 | `38.540687..46.588949` | 22.055 ms |
| `runDeficient` | 16, 24, 32, 48, 64, 96, 128 | +0.052627 | `23.025552..26.782321` | 39.276 ms |
| `runTall` | 8, 12, 16, 24, 32, 48, 64, 96, 128 | -0.116115 | `358.549467..472.150514` | 39.877 ms |
| `runConjugate` | 16, 24, 32, 48, 64, 96, 128 | +0.049200 | `16.455265..19.647626` | 36.103 ms |
| `runProfile` | 16, 24, 32, 48, 64, 96, 128 | +0.064514 | `11.198639..14.095147` | 37.372 ms |
| `runPrincipalDense` | 16, 24, 32, 48, 64, 96, 128 | -0.062951 | `25.816078..33.037103` | 37.305 ms |
| `runRankDense` | 16, 24, 32, 48, 64, 96, 128 | -0.040380 | `38.198808..46.483487` | 37.157 ms |
| `runBasisDense` | 16, 24, 32, 48, 64, 96, 128 | -0.045078 | `38.201266..47.128032` | 33.858 ms |
| `runDataDense` | 16, 24, 32, 48, 64, 96, 128 | -0.015568 | `83.965751..101.416789` | 35.154 ms |
| `runWithInvDense` | 16, 24, 32, 48, 64, 96, 128 | -0.040314 | `105.666640..126.194589` | 22.959 ms |
| `runCoeffsDense` | 16, 24, 32, 48, 64, 96, 128 | -0.010743 | `83.186980..100.847699` | 55.430 ms |
| `runContainsDense` | 16, 24, 32, 48, 64, 96, 128 | -0.012241 | `83.779357..101.055230` | 22.708 ms |
| `runKernelDeficient` | 16, 24, 32, 48, 64, 96, 128 | +0.023083 | `35.720584..39.961672` | 23.542 ms |
| `runPivotsDense` | 16, 24, 32, 48, 64, 96, 128 | -0.037427 | `38.306030..46.911315` | 25.145 ms |
| `runIndexDense` | 16, 24, 32, 48, 64, 96, 128 | -0.036276 | `38.231464..46.685346` | 25.532 ms |
| `runShapePrepared` | 16, 24, 32, 48, 64, 96, 128, 192, 256 | -0.061471 | `57.273815..67.419275` | 24.425 ms |
| `runCertPrepared` | 64, 96, 128, 192, 256, 384, 512 | -0.068331 | `76.174207..91.538947` | 23.210 ms |

Every fit uses the default policy of excluding only its first rung. In
particular, the tall verdict retains all nine raw rungs and fits 12 through
128 without special trimming. The largest three-trial spread is 22.531% at
`runProfile` 96; the median, adjacent rungs, and fitted verdict remain
consistent. The raw export preserves every trial, fit-inclusion flag,
constant, spread, and environment field.

Tall is the tightest verdict: its fitted slope is -0.116 against the ±0.15
window, while all nine raw rungs remain committed for reproduction on other
hosts.

The untimed growth runner scans the working matrix after every elementary
update and asserts that its final matrix equals public `Matrix.hnf`. Reproduce
the full timed-family ranges with:

```sh
lake exe hexhermite_bench growth conjugate 16 24 32 48 64 96 128
lake exe hexhermite_bench growth dense 8 12 16 24 32 48 64 96 128
lake exe hexhermite_bench growth deficient 8 12 16 24 32 48 64 96 128
lake exe hexhermite_bench growth tall 8 12 16 24 32 48 64 96 128
```

The committed [growth transcript](bench-results/hex-hermite-phase4-growth.txt)
records the original ranges at source commit
`136980ce850c3c89b7ed90902b07eb1318336dae` (content-identical rebased
commit `cd009ea9e5152ec048bf3bd91eecdaa304811939`) and the two extended tall
rungs at source commit `6f4360f29c1f1bce8f8981412f4e28d7ff55573a`
(content-identical rebased commit
`98926bd3757f38c071bc8102c25952ad38b3abbe`). It includes Lean and
LeanBench versions, host, OS, family, dimension, peak width, and output width;
its SHA-256 is
`40c1b4b1906a329890bc7e4bdea571493e5d1dc1d560c3c10284fda97ca261ab`.
Dense grows from 30/17 bits at `n=8` to 1375/691 at `n=128`, deficient
from 18/13 to 640/323, and tall from 6/4 to 14/8. Conjugate grows from
12/5 at `n=16` to 70/8 at `n=128`: peak width diverges materially from
output width. Its flat normalized wall ladder supports the calibrated log
factor but does not track the much steeper peak-width curve. The divergence
therefore satisfies the SPEC's predeclared trigger; issue #9689 records the bounded
Havas-Majewski-Matthews evaluation follow-up without adding that algorithm to
this release unit.

## Comparator ratios

The informational comparators are `FLINT fmpz_mat_hnf via python-flint`
(python-flint 0.9.0 / FLINT 3.6.0) and `PARI mathnf via cypari2`
(cypari2 2.2.4 / PARI 2.17.3). The clean fixed run used source commit
`bfc68387031a582cdbdd76ba6d84f0f047289c7d` (content-identical rebased
commit `cd16d1950ad21c5e29895c4a1f8120b178012992`) on the same host and toolchain:

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
`2dd6ad65396e109557c3056dea4508b8ae2681703c39d15d07944beedebee6d8`.
FLINT's no-work median is 7.145 us and PARI's is 7.061 us. Every external
median exceeds twice its own overhead, is below ten seconds, and agrees with
Lean's canonical HNF hash at all 20 common-domain points. Adjusted ratios
subtract only the matching external request/reply floor; serialization and
external matrix construction remain charged.

### Random dense Hermite

| n | Hex | FLINT | PARI | canonical hash | FLINT raw / adjusted | PARI raw / adjusted |
|---:|---:|---:|---:|---|---:|---:|
| 16 | 608.992 us | 125.268 us | 343.747 us | `0xd4c4d30cf11e3902` | 0.206x / 0.194x | 0.564x / 0.553x |
| 24 | 2.446 ms | 346.125 us | 867.055 us | `0xc2db6d9cd48562cf` | 0.141x / 0.139x | 0.354x / 0.352x |
| 32 | 6.546 ms | 760.868 us | 1.839 ms | `0x7dea452eb86f21c4` | 0.116x / 0.115x | 0.281x / 0.280x |
| 40 | 14.187 ms | 2.342 ms | 3.299 ms | `0x3e6a06331c9a70f5` | 0.165x / 0.165x | 0.233x / 0.232x |
| 48 | 25.670 ms | 2.885 ms | 4.899 ms | `0xf0b970d34f3479cf` | 0.112x / 0.112x | 0.191x / 0.191x |

Both external/Hex ratios decline overall; the FLINT threshold bump at 40 does
not support a crossover claim.

![Random dense comparator runtimes](figures/hex-hermite-comparator-random-dense-hermite.svg)

### Rank-deficient Hermite

| n | Hex | FLINT | PARI | canonical hash | FLINT raw / adjusted | PARI raw / adjusted |
|---:|---:|---:|---:|---|---:|---:|
| 16 | 271.570 us | 117.656 us | 307.491 us | `0x8c3b42aee1b184e` | 0.433x / 0.407x | 1.132x / 1.106x |
| 24 | 1.388 ms | 307.789 us | 874.446 us | `0x9a533e7da7244459` | 0.222x / 0.217x | 0.630x / 0.625x |
| 32 | 3.840 ms | 1.174 ms | 1.768 ms | `0xe5df8cb1544b5979` | 0.306x / 0.304x | 0.460x / 0.458x |
| 40 | 8.243 ms | 2.614 ms | 5.546 ms | `0x705d86c1ef31d9c9` | 0.317x / 0.316x | 0.673x / 0.672x |
| 48 | 14.069 ms | 4.623 ms | 5.928 ms | `0x98d873e64dfda3bc` | 0.329x / 0.328x | 0.421x / 0.421x |

The deficient ratios are nonmonotone after the initial drop, so five rungs
support no stronger crossover statement.

![Rank-deficient comparator runtimes](figures/hex-hermite-comparator-rank-deficient-hermite.svg)

### Tall Hermite

| n | Hex | FLINT | PARI | canonical hash | FLINT raw / adjusted | PARI raw / adjusted |
|---:|---:|---:|---:|---|---:|---:|
| 16 | 1.836 ms | 394.024 us | 1.009 ms | `0x8194afcd561bfd53` | 0.215x / 0.211x | 0.550x / 0.546x |
| 24 | 5.798 ms | 911.912 us | 3.564 ms | `0x720fca5c6fa3aec1` | 0.157x / 0.156x | 0.615x / 0.614x |
| 32 | 13.056 ms | 1.757 ms | 4.327 ms | `0x418e1a4c9e9d84b3` | 0.135x / 0.134x | 0.331x / 0.331x |
| 40 | 24.611 ms | 5.942 ms | 7.003 ms | `0x39dab28adc1593b5` | 0.241x / 0.241x | 0.285x / 0.284x |
| 48 | 41.678 ms | 9.625 ms | 10.405 ms | `0xb51a4d975bdc6feb` | 0.231x / 0.231x | 0.250x / 0.249x |

Hex remains slower at all five tall points. The DKT/modular question therefore
remains an algorithm-design question, not a reason to claim a measured
crossover for the current implementation.

![Tall comparator runtimes](figures/hex-hermite-comparator-tall-hermite.svg)

### Unimodular conjugate

| n | Hex | FLINT | PARI | canonical hash | FLINT raw / adjusted | PARI raw / adjusted |
|---:|---:|---:|---:|---|---:|---:|
| 16 | 288.452 us | 102.047 us | 310.240 us | `0x1b4006b1f4d4df66` | 0.354x / 0.329x | 1.076x / 1.051x |
| 24 | 1.391 ms | 231.378 us | 774.994 us | `0xe47f13aca06b7628` | 0.166x / 0.161x | 0.557x / 0.552x |
| 32 | 3.440 ms | 446.111 us | 1.649 ms | `0x531c1c24c585ac12` | 0.130x / 0.128x | 0.479x / 0.477x |
| 40 | 7.064 ms | 783.356 us | 2.760 ms | `0xfc1deb59344974c8` | 0.111x / 0.110x | 0.391x / 0.390x |
| 48 | 12.741 ms | 7.143 ms | 4.189 ms | `0x501203bf9b14db75` | 0.561x / 0.560x | 0.329x / 0.328x |

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
(content-identical rebased commit `9816d1e132bcc64339db28db14d6408a6ee44b6e`)
at 999 Hz on the same `chungus2` hardware, Lean 4.34.0-rc2, and LeanBench
0.1.0. Subsequent changes do not alter the profiled routes. Inputs are
deterministic: dense salt 5, deficient salt 17, full
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
