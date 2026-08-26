# HexSmith Performance Report

## Bench targets

The compiled Mathlib-free driver is `bench/HexSmith/Bench.lean`. Its adjacent
cost derivations register these parametric targets; the expressions below are
copied from the registration sites.

| target | input and public surface | declared complexity |
|---|---|---|
| `runDense` | square `snf` | `n ^ 3` |
| `runDenseTall` | 2:1 tall `snf` | `n ^ 3` |
| `runDenseWide` | 1:2 wide `snf` | `n ^ 3` |
| `runDenseDeficient` | rank-deficient square `snf` | `n ^ 3` |
| `runChain` | full-rank chain-conjugate `snf` | `n ^ 3` |
| `runChainDeficient` | rank-deficient chain-conjugate `snf` | `n ^ 3` |
| `runPresentation` | square presentation `snf` | `n ^ 3` |
| `runPresentationWide` | wide presentation `snf` | `n ^ 3` |
| `runRank` | `snfRank` | `n ^ 3` |
| `runInvariantFactors` | `invariantFactors` | `n ^ 3` |
| `runData` | transform-producing `snfData` | `n ^ 3` |
| `runSmithBasis` | executable `smithBasis` | `n ^ 3` |
| `runAbelianStructure` | presentation `abelianStructure` | `n ^ 3` |
| `runShape` | prepared-certificate `isSNFShape` | `n` |
| `runCert` | prepared-certificate `snfCert` | `n ^ 2` |
| `runDiagonal` | form-only `snfDiagonal` | `n ^ 2` |
| `runDiagonalGeneral` | general `snf` on the same diagonal | `n ^ 3` |
| `runDiagonalData` | transform-producing `snfDiagonalData` | `n ^ 3` |

The fixed registrations cover Lean, FLINT, and PARI on five common-domain
rungs for each declared family: dense and chain-conjugate dimensions
`#[6, 8, 10, 12, 14]`, and presentation dimensions
`#[8, 12, 16, 20, 24]`. `runFlintOverhead` and `runPariOverhead` are no-work
persistent-driver calibration targets. Every fixed target has an expected
hash obtained from the independent external result. `detDivisor` is the
SPEC's noncomputable uniqueness surface, whose direct minor enumeration is
exponential; it deliberately has no runtime registration.

The deterministic constructor salts are the literal constants in
`bench/HexSmith/Bench.lean`: dense shapes use `11`, `23`, `37`, and `47`;
chain-conjugate row and column operations use `73` and `97`; presentation
entries are a fixed sparse recurrence and have no random seed.

## Verdicts

The scientific run used source commit
`32aeeffbf44f2d9704d42d260f396eb70e409220`, Lean 4.34.0-rc2, LeanBench
0.1.0, and warm-cache compiled execution from a clean tree (`git_dirty=false`)
on `chungus2` (Linux 6.12.100,
x86-64, AMD EPYC 9455 48-Core Processor, 96 logical CPUs). Each registration
used its committed ladder, three outer trials, a 100 ms inner target, a 1.0
spawn-floor multiplier, a 10 s per-call ceiling, and the registration's
committed warmup fraction:

```sh
lake exe hexsmith_bench run \
  Hex.SmithBench.runDense Hex.SmithBench.runDenseTall \
  Hex.SmithBench.runDenseWide Hex.SmithBench.runDenseDeficient \
  Hex.SmithBench.runChain Hex.SmithBench.runChainDeficient \
  Hex.SmithBench.runPresentation Hex.SmithBench.runPresentationWide \
  Hex.SmithBench.runRank Hex.SmithBench.runInvariantFactors \
  Hex.SmithBench.runData Hex.SmithBench.runSmithBasis \
  Hex.SmithBench.runAbelianStructure Hex.SmithBench.runShape \
  Hex.SmithBench.runCert Hex.SmithBench.runDiagonal \
  Hex.SmithBench.runDiagonalGeneral Hex.SmithBench.runDiagonalData \
  --export-file reports/bench-results/hex-smith-phase4-scientific.json
```

The committed export is
`reports/bench-results/hex-smith-phase4-scientific.json`, SHA-256
`e28f17f192716e0f8b01f02c129031a36a51034d30c76f90db2dca25842cae68`.
Every rung cleared the signal filter and every target was consistent with its
declared complexity:

| target | ladder | verdict details |
|---|---|---|
| `runDense` | 4, 6, 8, 10, 12, 14 | consistent; `cMin=142.776`, `cMax=183.523` |
| `runDenseTall` | 3, 4, 5, 6, 8, 10 | consistent; `cMin=346.055`, `cMax=497.223` |
| `runDenseWide` | 3, 4, 5, 6, 8, 10 | consistent; `cMin=290.346`, `cMax=390.470` |
| `runDenseDeficient` | 4, 6, 8, 10, 12, 14 | consistent; `cMin=65.700`, `cMax=94.533` |
| `runChain` | 4, 6, 8, 10, 12, 14 | consistent; `cMin=63.822`, `cMax=75.235` |
| `runChainDeficient` | 4, 6, 8, 10, 12, 14 | consistent; `cMin=53.934`, `cMax=71.005` |
| `runPresentation` | 16, 24, 32, 48, 64, 96 | consistent; `beta=-0.101` |
| `runPresentationWide` | 16, 24, 32, 48, 64, 96 | consistent; `beta=-0.126` |
| `runRank` | 4, 6, 8, 10, 12, 14 | consistent; `cMin=143.075`, `cMax=184.064` |
| `runInvariantFactors` | 4, 6, 8, 10, 12, 14 | consistent; `cMin=143.880`, `cMax=182.465` |
| `runData` | 4, 6, 8, 10, 12 | consistent; `cMin=250.845`, `cMax=357.913` |
| `runSmithBasis` | 4, 6, 8, 10, 12 | consistent; `cMin=402.876`, `cMax=572.521` |
| `runAbelianStructure` | 16, 24, 32, 48, 64, 96 | consistent; `beta=-0.140` |
| `runShape` | 32, 64, 128, 256, 512, 1024 | consistent; `beta=-0.009` |
| `runCert` | 16, 24, 32, 48, 64, 96 | consistent; `cMin=931.057`, `cMax=998.407` |
| `runDiagonal` | 8, 12, 16, 24, 32, 48, 64 | consistent; `beta=-0.118` |
| `runDiagonalGeneral` | 8, 12, 16, 24, 32, 48, 64 | consistent; `beta=-0.063` |
| `runDiagonalData` | 16, 24, 32, 48, 64, 96, 128 | consistent; `cMin=16.219`, `cMax=19.033` |

The ladder column lists every measured rung. The harness computes each printed
verdict after the registration's declared leading warmup fraction: 0.2 for the
ordinary dense/chain/projection/diagonal routes, 0.3 for the presentation
routes, and 0.5 for `runCert` and `runDiagonalData`. Thus, for example,
`runCert`'s displayed band is the verdict window `n=48,64,96`, not a claim that
the omitted warmup rungs have the same normalised constant. The upward
pre-window drift is expected while the packed certificate operands acquire
their linear bit width; all raw rung constants and inclusion flags are in the
committed export.

The internal paired medians in that same export answer the two route-cost
questions. `snfData / snf` rises from 1.485x at `n=4` through 1.721x,
1.810x, and 2.157x to 2.184x at `n=12`. On common diagonal rungs
`n=16,24,32,48,64`, general `snf / snfDiagonal` is respectively
26.819x, 41.491x, 57.311x, 87.467x, and 120.622x; the advantage grows
strongly, proving that the diagonal route bypasses elimination.
`snfDiagonalData / snfDiagonal` is 15.558x, 20.829x, 25.897x, 35.447x,
and 46.066x on those rungs, exposing transform accumulation separately.

The untimed coefficient-growth command was:

```sh
lake exe hexsmith_bench growth \
  > reports/bench-results/hex-smith-phase4-growth.csv
```

Its committed output has SHA-256
`f9a17266194c37a3221cc2124b4c80391fec1f435d6b422861c66542f769a109`.
At `n=12`, peak/output bit widths were 1080/103 for dense square,
857/1 for tall, 1917/1 for wide, and 202/1 for rank-deficient inputs;
chain-conjugate square and rank-deficient inputs were 19/13 and 17/10.
The presentation ladder reached 104/104 bits for square `n=24` and 53/1
for wide `n=24`. The full curve for every preceding rung is in the CSV.

The dense family confirms that the classical pivot loop can grow entries
substantially, but its controlled wall-clock ladders remain stable and
consistent with the declared cubic matrix-update model. That evidence does
not justify adding Kannan--Bachem now. Iliopoulos is also not selected: its
nonsingular-square diagonal-output domain would not serve the required
rectangular, rank-deficient, transform, system, or presentation surfaces.
Presentation growth is modest and the downstream-wide `n=96` route remains
consistent with its declared dense cubic model, so a sparse Smith algorithm
is not a release requirement; it remains future work if downstream sizes make
the measured dense path inadequate.

The repair-heavy diagonal ladder deliberately holds operand width at `O(1)`
with entries from `{2, -1, 0}`. Its quadratic verdict therefore isolates the
fixed pair count, array routing, dense result materialisation, and hashing; it
does not claim a bit-complexity bound for growing diagonal entries. The SPEC's
separate operand-size statement remains "bounded by the product of the input
diagonal".

## Comparator ratios

The registry's exact comparator names are `FLINT fmpz_mat_snf via python-flint`
and `PARI matsnf via cypari2`. FLINT uses python-flint 0.9.0 / FLINT 3.6.0;
PARI uses cypari2 2.2.4 / PARI 2.17.3. Both are informational comparators with
different tuned dispatch policies. The fixed run used five measured repeats
per target and the persistent JSON-line drivers:

```sh
nix-shell -p python313Packages.cypari2 python313Packages.cysignals pari --run '
  export HEX_FLINT_BENCH_PYTHON=/tmp/hexsmith-py/bin/python
  export HEX_PARI_BENCH_PYTHON=/tmp/hexsmith-py/bin/python
  fixed=$(lake exe hexsmith_bench list | awk '\''/\[fixed\]/ {print $1}'\'')
  lake exe hexsmith_bench run $fixed \
    --export-file reports/bench-results/hex-smith-phase4-comparators.json
'
```

The committed 47-target export is
`reports/bench-results/hex-smith-phase4-comparators.json`, SHA-256
`b61d716b616136012fb9163ee45794d01dc8750e8a6cf5c3a8bd4a43d7a81186`.
All repeats matched their expected hashes. `compare` was also run for each of
the 15 triples by replacing `SPEC` below with every suffix in
`{Dense6,Dense8,Dense10,Dense12,Dense14,Chain6,Chain8,Chain10,Chain12,
Chain14,Presentation8,Presentation12,Presentation16,Presentation20,
Presentation24}`; all 15 reported output agreement:

```sh
lake exe hexsmith_bench compare \
  Hex.SmithBench.runHexSPEC Hex.SmithBench.runFlintSPEC \
  Hex.SmithBench.runPariSPEC
```

The no-work medians were 7.141 us for FLINT and 7.001 us for PARI. All
15 rungs are eligible: each external median is at least twice its own
overhead and every per-call median is below 1 s. Tables give raw and
overhead-adjusted `external / Hex` ratios; subtraction removes only the
constant request/reply floor, so input encoding and external matrix
construction remain charged to the comparator.

### Random dense Smith

| n | Hex | FLINT | PARI | canonical hash | FLINT raw / adjusted | PARI raw / adjusted |
|---:|---:|---:|---:|---|---:|---:|
| 6 | 31.451 us | 19.243 us | 45.299 us | `0xf04520317df0def8` | 0.612x / 0.385x | 1.440x / 1.218x |
| 8 | 72.647 us | 28.228 us | 70.807 us | `0xe4073bf661a3c59a` | 0.389x / 0.290x | 0.975x / 0.878x |
| 10 | 163.626 us | 48.349 us | 120.986 us | `0xf68ae7878c8af87b` | 0.295x / 0.252x | 0.739x / 0.697x |
| 12 | 289.111 us | 66.586 us | 170.585 us | `0x5e971675ada9d783` | 0.230x / 0.206x | 0.590x / 0.566x |
| 14 | 532.740 us | 90.280 us | 248.183 us | `0x699fd5ab6f700da0` | 0.169x / 0.156x | 0.466x / 0.453x |

Both adjusted ratios decline monotonically. At the top rung FLINT is about
6.4x faster and PARI about 2.2x faster. This expected informational divergence
is consistent with tuned external dispatch versus the classical Lean pivot
loop and is not a gating Concern.

![Random dense comparator runtimes](figures/hex-smith-comparator-random-dense-smith.svg)

### Chain conjugate

| n | Hex | FLINT | PARI | canonical hash | FLINT raw / adjusted | PARI raw / adjusted |
|---:|---:|---:|---:|---|---:|---:|
| 6 | 16.393 us | 18.517 us | 42.662 us | `0x1e5b9e22113b8d71` | 1.130x / 0.694x | 2.602x / 2.175x |
| 8 | 35.608 us | 25.481 us | 69.135 us | `0xb3713c08af9eb87c` | 0.716x / 0.515x | 1.942x / 1.745x |
| 10 | 67.663 us | 33.207 us | 117.173 us | `0xefcb83d9d11c9839` | 0.491x / 0.385x | 1.732x / 1.628x |
| 12 | 112.656 us | 44.637 us | 208.251 us | `0x239317e249e653d3` | 0.396x / 0.333x | 1.849x / 1.786x |
| 14 | 174.930 us | 56.766 us | 303.054 us | `0x049888f934ad3581` | 0.325x / 0.284x | 1.732x / 1.692x |

FLINT's adjusted ratio falls steadily to 0.284x. PARI remains slower than Hex
throughout the adjusted ladder, settling near 1.63--1.79x after `n=8`; the
small reversal at `n=12` is a local constant-factor variation rather than a
change in the overall plateau. Neither informational comparator imposes a
threshold.

![Chain-conjugate comparator runtimes](figures/hex-smith-comparator-chain-conjugate.svg)

### Presentation Smith

| n | Hex | FLINT | PARI | canonical hash | FLINT raw / adjusted | PARI raw / adjusted |
|---:|---:|---:|---:|---|---:|---:|
| 8 | 39.913 us | 24.565 us | 52.961 us | `0x82b42ad65a90f9be` | 0.615x / 0.437x | 1.327x / 1.152x |
| 12 | 116.010 us | 43.106 us | 102.891 us | `0xfc1472e454f53028` | 0.372x / 0.310x | 0.887x / 0.827x |
| 16 | 249.045 us | 68.187 us | 173.358 us | `0x47ef2f14529c425f` | 0.274x / 0.245x | 0.696x / 0.668x |
| 20 | 472.555 us | 104.340 us | 273.833 us | `0x032c9800f08ccd0d` | 0.221x / 0.206x | 0.579x / 0.565x |
| 24 | 779.906 us | 148.392 us | 385.521 us | `0xb281650658ac39a7` | 0.190x / 0.181x | 0.494x / 0.485x |

Both adjusted ratios decline monotonically over the five-rung eligible range;
at `n=24`, FLINT is about 5.5x faster and PARI about 2.1x faster. The trend is
expected for the dense classical route against separately tuned external
implementations and is informational.

![Presentation comparator runtimes](figures/hex-smith-comparator-presentation-smith.svg)

## Profile

One representative case was sampled for every `libraries.yml` input family.
The presentation-wide case is the downstream-realistic hot path; the dense
family separately has the worst top-rung comparator gap. All profiles used source
commit `32aeeffbf44f2d9704d42d260f396eb70e409220`, the same host and LeanBench
environment as the scientific run, also from a clean tree, with samply 0.13.1
at 999 Hz and this command shape:

```sh
LEAN_BENCH_SAMPLY_HOME=/tmp/lean-bench-samply \
  scripts/profile/run_profile.sh .lake/build/bin/hexsmith_bench TARGET PARAM 5000000000
```

Raw filtered profiles are developer-local under `/tmp` and are not committed,
as required by `SPEC/profiling.md`. Percentages below are derived by
`scripts/profile/summarize_profile.py --thread hexsmith_bench`; the four
required leaf categories classify at least 99.59% of every profile.

The prepared `runShape`/`runCert` certificate uses identity transforms and a
constant diagonal so that every checker conjunct executes without timing an
`snfData` preparation. These measurements are a controlled checker floor;
transform-heavy end-to-end cost is represented separately by `runData` and
`runSmithBasis`.

### Random dense Smith

`TARGET=Hex.SmithBench.runDense`, `PARAM=14`, seed/salt 11. The filtered
profile `/tmp/hex-profile-runDense-14.json.gz` retained 4111 samples. Leaf
cost was allocation/free 43.64%, GMP 16.93%, Lean runtime 34.01%, Hex own code
5.25%, and other 0.17%.

| inclusive Hex function | share |
|---|---:|
| `Hex.SmithBench.runDense` | 97.18% |
| `Hex.Matrix.snf` | 96.59% |
| `Hex.Matrix.Smith.runFuel` | 96.55% |
| `Hex.Matrix.Smith.reduceFuel` | 75.55% |
| `Hex.Matrix.Smith.clearColumn` | 33.62% |
| `Hex.Matrix.Smith.clearRow` | 16.15% |
| `Hex.Matrix.Smith.findBad?` | 15.20% |

This is the registered dense form-only route. Reduction and row/column
clearing dominate, while GMP and allocation reflect the measured growth of
intermediate integer entries.

```text
calibration residual: 1.424 ms (limit 5 ms)
total timed: 4142.5 ms
retained samples: 4111 (8 rejected outside windows)
sensitivity +/-5 ms: passed
confidence: passed
```

### Chain conjugate

`TARGET=Hex.SmithBench.runChain`, `PARAM=14`, deterministic conjugation salts
73 and 97. `/tmp/hex-profile-runChain-14.json.gz` retained 2795 samples. Leaf
cost was allocation/free 33.49%, GMP 0.00%, Lean runtime 60.93%, Hex own code
5.19%, and other 0.39%.

| inclusive Hex function | share |
|---|---:|
| `Hex.SmithBench.runChain` | 99.89% |
| `Hex.Matrix.snf` | 98.46% |
| `Hex.Matrix.Smith.runFuel` | 98.43% |
| `Hex.Matrix.Smith.reduceFuel` | 57.03% |
| `Hex.Matrix.Smith.findBad?` | 37.21% |
| `Hex.Matrix.Smith.findPivot?` | 37.32% |
| `Hex.Matrix.Smith.clearColumn` | 10.95% |

The registered chain route dominates. Its small coefficients make runtime
dispatch, scanning, and allocation more visible than GMP arithmetic; pivot and
divisibility searches are the main inclusive subpaths.

```text
calibration residual: 2.510 ms (limit 5 ms)
total timed: 2836.4 ms
retained samples: 2795 (9 rejected outside windows)
sensitivity +/-5 ms: passed
confidence: passed
```

### Presentation Smith

`TARGET=Hex.SmithBench.runPresentationWide`, `PARAM=96`, fixed sparse
recurrence with no random seed. `/tmp/hex-profile-runPresentationWide-96.json.gz`
retained 2910 samples. Leaf cost was allocation/free 36.49%, GMP 0.38%, Lean
runtime 62.41%, Hex own code 0.72%, and other 0.00%.

| inclusive Hex function | share |
|---|---:|
| `Hex.SmithBench.runPresentationWide` | 99.97% |
| `Hex.Matrix.snf` | 99.76% |
| `Hex.Matrix.Smith.runFuel` | 99.76% |
| `Hex.Matrix.Smith.reduceFuel` | 54.91% |
| `Hex.Matrix.Smith.findBad?` | 50.41% |
| `Hex.Matrix.Smith.findPivot?` | 43.85% |

The downstream presentation target is directly responsible for the profile.
The sparse input is deliberately routed through the dense v1 engine; repeated
trailing-block scans, not an unregistered preprocessing step, dominate.

```text
calibration residual: 0.240 ms (limit 5 ms)
total timed: 2931.1 ms
retained samples: 2910 (14 rejected outside windows)
sensitivity +/-5 ms: passed
confidence: passed
```

No dominant inclusive cost in any family lies outside a registered target.
`HexSmithMathlib` is a `correspondence-only-layer`: it performs no independent
runtime computation and names `HexSmith` as its Phase-4 performance owner, so
it has no synthetic benchmark or separate report.

## Concerns

None.
