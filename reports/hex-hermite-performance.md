# HexHermite Performance Report

## Bench targets

The compiled Mathlib-free driver is `bench/HexHermite/Bench.lean`. Its four
parametric registrations exercise `Matrix.hnf` on every input family declared
in `libraries.yml`:

| target | input family and shape | declared scientific model |
|---|---|---|
| `runDense` | `random-dense-hermite`, square and nonsingular | `n ^ 3 * Nat.log2 (n + 1)` |
| `runDeficient` | `rank-deficient-hermite`, square with rank `n / 2` | `n ^ 3 * Nat.log2 (n + 1)` |
| `runTall` | `tall-hermite`, `4n × n` with redundant rows | `n ^ 3` |
| `runConjugate` | `unimodular-conjugate`, pseudo-random unit-lower-triangular factor times known diagonal | `n ^ 3` |

For dense and rank-deficient inputs, the adjacent derivation charges cubic
matrix-entry visits and a logarithmic Euclidean operand factor. Tall and
conjugate inputs keep coefficients controlled, so their adjacent derivations
charge cubic entry visits. These are controlled-family wall-clock models; the
SPEC separately retains the conservative `O(n⁴)` unrestricted worst-case
ceiling obtained by charging every scheduled reduction check as a nontrivial
full-row update.

The public executable surface that does not naturally vary in dimension has
fixed evidence:

| targets | public operations |
|---|---|
| `runIsHNFForm`, `runCert` | HNF shape checking and certificate replay |
| `runRank`, `runBasis`, `runPivots`, `runIndex` | rank, canonical basis, pivots, and lattice index |
| `runData`, `runWithInv` | transform-producing data and inverse accumulation |
| `runCoeffs`, `runCoeffsMiss`, `runContains`, `runContainsMiss` | successful and unsuccessful constructive coefficients and membership |
| `runKernelBasis` | executable integer kernel basis on a rank-deficient input with a nonempty kernel |

All fixed API targets have committed expected structural hashes. The external
comparison surface has five rungs, `#[16, 24, 32, 40, 48]`, for every declared
family and registers Lean, FLINT, and PARI separately. `runFlintOverhead` and
`runPariOverhead` measure the persistent-driver request/reply floor. Comparator
hashes cover only the canonical HNF matrix; non-unique transforms and inverses
are checked in Lean by conformance and certificate replay.

The input constructors are deterministic. `entry` uses literal salts `5` and
`17`; the conjugate family uses salt `41` for a bounded pseudo-random
unit-lower-triangular factor. No runtime seed is required.

## Verdicts

The scientific run used source commit
`151bb177a476d2dd23e50c4f6c6d9a93d953a928`, Lean 4.34.0-rc2,
LeanBench 0.1.0, and warm-cache compiled execution from a clean tree
(`git_dirty=false`) on `chungus2` (Linux x86-64, AMD EPYC 9455 48-Core
Processor, 96 logical CPUs). Each target used its committed seven-rung ladder,
three outer trials, the default two-second inner target and spawn-floor filter,
and a ten-second per-call ceiling:

```sh
lake exe hexhermite_bench run \
  Hex.HermiteBench.runDense Hex.HermiteBench.runDeficient \
  Hex.HermiteBench.runTall Hex.HermiteBench.runConjugate \
  --export-file reports/bench-results/hex-hermite-phase4-scientific.json
```

The committed export has SHA-256
`70341a43024a49676ab9db3701703318d275fa3138aafad41418cfd53edbae17`.
Every target is consistent with its declared complexity and has a fitted
log-log slope:

| target | full measured ladder | fitted slope | verdict window | spawn floor |
|---|---|---:|---|---:|
| `runDense` | 16, 24, 32, 48, 64, 96, 128 | -0.073607 | consistent; `cMin=41.781987`, `cMax=51.772352` | 22.140 ms |
| `runDeficient` | 16, 24, 32, 48, 64, 96, 128 | +0.023776 | consistent; `cMin=24.710523`, `cMax=27.878874` | 22.020 ms |
| `runTall` | 8, 12, 16, 24, 32, 48, 64 | -0.146000 | consistent; `cMin=430.245663`, `cMax=547.112288` | 23.394 ms |
| `runConjugate` | 16, 24, 32, 48, 64, 96, 128 | +0.100045 | consistent; `cMin=86.960072`, `cMax=102.994449` | 36.173 ms |

The harness excludes the leading warmup rung from each printed verdict. Every
rung cleared the signal-floor filter. The largest trial spread was 4.987% at
`runTall 48`; all raw trials, inclusion flags, constants, and environment data
are in the export.

The SPEC's untimed coefficient-growth instrumentation was reproduced with:

```sh
lake exe hexhermite_bench growth 16 24 32 48 64 96 128 \
  > reports/bench-results/hex-hermite-phase4-growth.txt
```

The output has SHA-256
`b20fac39a4306dd2cd551a8eae4925c878f8ece9630ed2b56a515b8076d0a64b`.
On the pseudo-random `unimodular-conjugate` ladder, peak/output entry widths
were respectively 8/5, 8/5, 9/6, 9/6, 10/7, 10/7, and 11/8 bits. Peak width
remains close to output width, and the wall-clock curve remains consistent
with its cubic declaration. The predeclared trigger for an LLL-based
Havas--Majewski--Matthews follow-up is therefore not met.

## Comparator ratios

The registry's exact informational comparators are
`FLINT fmpz_mat_hnf via python-flint` and `PARI mathnf via cypari2`. The run
used python-flint 0.9.0 / FLINT 3.6.0 and cypari2 2.2.4 / PARI 2.17.3. The
fixed targets were reproduced from the clean source commit with five repeats
each:

```sh
nix-shell -p python313Packages.cypari2 python313Packages.cysignals pari --run '
  export HEX_FLINT_BENCH_PYTHON=/tmp/hexsmith-py/bin/python
  export HEX_PARI_BENCH_PYTHON=/tmp/hexsmith-py/bin/python
  fixed=$(lake exe hexhermite_bench list | awk '\''/\[fixed\]/ {print $1}'\'')
  lake exe hexhermite_bench run $fixed \
    --export-file reports/bench-results/hex-hermite-phase4-comparators.json
'
```

The committed 75-target export has SHA-256
`8ad7485196c9dec7fbaf974c44230e73087f3a0f3cf5104af78db23edef9eec9`;
every expected hash matches every observed and repeated hash. Those committed
rows independently substantiate the canonical-output agreement also reported
by `compare` for all twenty suffixes in
`{Dense,Deficient,Tall,Conjugate}{16,24,32,40,48}`:

```sh
lake exe hexhermite_bench compare \
  Hex.HermiteBench.runHexSUFFIX Hex.HermiteBench.runFlintSUFFIX \
  Hex.HermiteBench.runPariSUFFIX
```

FLINT's no-work median was 7.051 us and PARI's was 7.005 us. Every external
median exceeds twice its own overhead and every per-call median is below ten
seconds, so all rungs are eligible. Adjusted ratios subtract only the constant
request/reply floor; direct JSON encoding and external matrix construction
remain charged.

### Random dense Hermite

| n | Hex | FLINT | PARI | canonical hash | FLINT raw / adjusted | PARI raw / adjusted |
|---:|---:|---:|---:|---|---:|---:|
| 16 | 743.101 us | 121.913 us | 346.779 us | `0xd4c4d30cf11e3902` | 0.164x / 0.155x | 0.467x / 0.457x |
| 24 | 2.846 ms | 342.613 us | 867.215 us | `0xc2db6d9cd48562cf` | 0.120x / 0.118x | 0.305x / 0.302x |
| 32 | 7.422 ms | 752.250 us | 1.831 ms | `0x7dea452eb86f21c4` | 0.101x / 0.100x | 0.247x / 0.246x |
| 40 | 15.887 ms | 2.359 ms | 3.373 ms | `0x3e6a06331c9a70f5` | 0.148x / 0.148x | 0.212x / 0.212x |
| 48 | 28.581 ms | 2.905 ms | 4.853 ms | `0xf0b970d34f3479cf` | 0.102x / 0.101x | 0.170x / 0.170x |

![Random dense comparator runtimes](figures/hex-hermite-comparator-random-dense-hermite.svg)

### Rank-deficient Hermite

| n | Hex | FLINT | PARI | canonical hash | FLINT raw / adjusted | PARI raw / adjusted |
|---:|---:|---:|---:|---|---:|---:|
| 16 | 312.616 us | 117.652 us | 307.853 us | `0x8c3b42aee1b184e` | 0.376x / 0.354x | 0.985x / 0.962x |
| 24 | 1.515 ms | 302.468 us | 878.061 us | `0x9a533e7da7244459` | 0.200x / 0.195x | 0.579x / 0.575x |
| 32 | 4.126 ms | 1.167 ms | 2.204 ms | `0xe5df8cb1544b5979` | 0.283x / 0.281x | 0.534x / 0.532x |
| 40 | 8.753 ms | 2.589 ms | 5.067 ms | `0x705d86c1ef31d9c9` | 0.296x / 0.295x | 0.579x / 0.578x |
| 48 | 14.984 ms | 4.595 ms | 5.848 ms | `0x98d873e64dfda3bc` | 0.307x / 0.306x | 0.390x / 0.390x |

![Rank-deficient comparator runtimes](figures/hex-hermite-comparator-rank-deficient-hermite.svg)

### Tall Hermite

| n | Hex | FLINT | PARI | canonical hash | FLINT raw / adjusted | PARI raw / adjusted |
|---:|---:|---:|---:|---|---:|---:|
| 16 | 2.135 ms | 393.097 us | 1.007 ms | `0x8194afcd561bfd53` | 0.184x / 0.181x | 0.472x / 0.469x |
| 24 | 6.721 ms | 933.018 us | 4.166 ms | `0x720fca5c6fa3aec1` | 0.139x / 0.138x | 0.620x / 0.619x |
| 32 | 14.983 ms | 1.757 ms | 4.349 ms | `0x418e1a4c9e9d84b3` | 0.117x / 0.117x | 0.290x / 0.290x |
| 40 | 28.522 ms | 5.937 ms | 7.031 ms | `0x39dab28adc1593b5` | 0.208x / 0.208x | 0.247x / 0.246x |
| 48 | 48.416 ms | 9.651 ms | 10.442 ms | `0xb51a4d975bdc6feb` | 0.199x / 0.199x | 0.216x / 0.216x |

![Tall comparator runtimes](figures/hex-hermite-comparator-tall-hermite.svg)

### Unimodular conjugate

| n | Hex | FLINT | PARI | canonical hash | FLINT raw / adjusted | PARI raw / adjusted |
|---:|---:|---:|---:|---|---:|---:|
| 16 | 361.796 us | 108.258 us | 297.748 us | `0x1b4006b1f4d4df66` | 0.299x / 0.280x | 0.823x / 0.804x |
| 24 | 1.243 ms | 286.206 us | 729.301 us | `0xe47f13aca06b7628` | 0.230x / 0.225x | 0.587x / 0.581x |
| 32 | 2.947 ms | 392.421 us | 1.593 ms | `0x531c1c24c585ac12` | 0.133x / 0.131x | 0.541x / 0.538x |
| 40 | 5.852 ms | 634.871 us | 2.599 ms | `0xfc1deb59344974c8` | 0.108x / 0.107x | 0.444x / 0.443x |
| 48 | 10.322 ms | 6.222 ms | 4.032 ms | `0x501203bf9b14db75` | 0.603x / 0.602x | 0.391x / 0.390x |

These informational ratios are measured on the same honest input domains and
include serialization and matrix construction. They are not gating speedup
claims.

![Unimodular-conjugate comparator runtimes](figures/hex-hermite-comparator-unimodular-conjugate.svg)

## Profile

Every `libraries.yml` input family was profiled from the same clean source
commit and host as the scientific run, with samply 0.13.1 at 999 Hz:

```sh
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply \
  scripts/profile/run_profile.sh .lake/build/bin/hexhermite_bench TARGET PARAM 5000000000
```

Raw filtered profiles are developer-local under `/tmp`, as required by
`SPEC/profiling.md`. Percentages were produced by
`scripts/profile/summarize_profile.py --thread hexhermite_bench`.

### Random dense Hermite

`TARGET=Hex.HermiteBench.runDense`, `PARAM=128`. The profile retained 5525
samples and rejected 15. Leaf cost was allocation/free 48.94%, GMP 21.18%,
Lean runtime 20.87%, Hex own code 8.80%, and other 0.22% (99.78% classified).

| inclusive Hex function | share |
|---|---:|
| `Hex.HermiteBench.runDense` | 96.47% |
| `Hex.Matrix.hnf` | 96.45% |
| `Hex.Matrix.Hermite.checkedRun` | 96.45% |
| `Hex.Matrix.Hermite.principalCore` | 59.19% |
| `Hex.Matrix.Hermite.clearPrior` | 47.40% |
| `Hex.Matrix.Hermite.normalizeRow` | 33.81% |
| `Hex.Matrix.Hermite.reduceStep` | 32.43% |

`principalCore`, `clearPrior`, and `reduceStep` perform the canonical principal
reductions. Immutable row updates allocate arrays, while growing `Int`
coefficients account for the visible GMP share. Calibration residual was
0.549 ms, total timed work 5548.2 ms, and sensitivity and confidence checks
passed.

### Rank-deficient Hermite

`TARGET=Hex.HermiteBench.runDeficient`, `PARAM=128`. The profile retained
3348 samples and rejected 18. Leaf cost was allocation/free 57.38%, GMP
20.01%, Lean runtime 16.19%, and Hex own code 6.42% (100.00% classified).

| inclusive Hex function | share |
|---|---:|
| `Hex.HermiteBench.runDeficient` | 98.09% |
| `Hex.Matrix.Hermite.checkedRun` | 97.76% |
| `Hex.Matrix.hnf` | 97.76% |
| `Hex.Matrix.Hermite.principalCore` | 63.14% |
| `Hex.Matrix.Hermite.clearPrior` | 56.33% |
| `Hex.Matrix.Hermite.gcdStep` | 41.79% |
| `Hex.Matrix.Hermite.combineRows` | 41.40% |
| `Hex.Matrix.ofFn` | 28.02% |

`gcdStep` and `combineRows` reconstruct dependent rows during principal
reduction. `Matrix.ofFn` is reached inside the registered HNF/rank-profile
path, so its allocation is charged to this target. Calibration residual was
0.694 ms, total timed work 3364.9 ms, and both checks passed.

### Tall Hermite

`TARGET=Hex.HermiteBench.runTall`, `PARAM=64`. The profile retained 3726
samples and rejected 7. Leaf cost was allocation/free 9.98%, GMP 0.00%, Lean
runtime 65.65%, and Hex own code 24.37% (100.00% classified).

| inclusive Hex function | share |
|---|---:|
| `Hex.HermiteBench.runTall` | 100.00% |
| `Hex.Matrix.Hermite.checkedRun` | 99.92% |
| `Hex.Matrix.hnf` | 99.92% |
| `Hex.Matrix.Hermite.principalCore` | 69.81% |
| `Hex.Matrix.Hermite.clearPrior` | 69.00% |
| `Hex.Matrix.Hermite.normalizeRow` | 38.75% |
| `Hex.Matrix.Hermite.gcdStep` | 28.31% |

`clearPrior`, `normalizeRow`, and `gcdStep` clear the redundant rows. The
family keeps coefficients tiny, so traversal of many small boxed values is
charged to the Lean runtime while GMP is absent. Calibration residual was
0.510 ms, total timed work 3744.6 ms, and both checks passed.

### Unimodular conjugate

`TARGET=Hex.HermiteBench.runConjugate`, `PARAM=128`. The profile retained
3709 samples and rejected 7. Leaf cost was allocation/free 20.76%, GMP
14.18%, Lean runtime 42.22%, Hex own code 22.76%, and other 0.08% (99.92%
classified).

| inclusive Hex function | share |
|---|---:|
| `Hex.HermiteBench.runConjugate` | 97.63% |
| `Hex.Matrix.hnf` | 97.55% |
| `Hex.Matrix.Hermite.checkedRun` | 97.55% |
| `Hex.Matrix.Hermite.profileStep` | 47.59% |
| `Hex.Matrix.ofFn` | 42.63% |
| `Hex.Matrix.Hermite.profileEliminate` | 38.64% |
| `Hex.Matrix.Hermite.principalCore` | 25.21% |

`profileStep`, `profileEliminate`, and `Matrix.ofFn` implement the
fraction-free rank-profile stage inside `Matrix.hnf`; this is registered-target
work, not unmeasured preprocessing. Calibration residual was 0.679 ms, total
timed work 3727.9 ms, and both checks passed.

`HexHermiteMathlib` is a `correspondence-only-layer`: it owns no independent
runtime computation, names `HexHermite` as its performance owner, and therefore
has no synthetic benchmark or separate performance report.

## Concerns

None.
