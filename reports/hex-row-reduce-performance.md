# HexRowReduce Performance Report

`HexRowReduce` provides exact row reduction, rank, span membership and
coefficients, nullspace construction, field inverse, and complete affine solving
with inconsistency witnesses over the `HexMatrix` dense core. Its
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

### Field inverse and solve targets

The `field-inverse-solve` family adds 119 parametric registrations in
`Hex.RowReduceBench.Field`: 85 dimension registrations with the source model
`n ^ 3`, and 34 fixed-dimension height registrations with `n ^ 2`.
The [field registration table](bench-results/hex-row-reduce-fields-verdicts.md)
lists every exact target name, model, selected mode, and scientific verdict.

Each carrier/height or fixed dimension has 17 registrations: `Full`,
`Deficient` (rank n−1), and `Half` (rank n/2) each exercise `Solve`, `Option`,
and `Inverse`; `DeficientError`, `HalfError`, `Tall`, and `Wide` exercise `Solve`
and `Option`. These suffixes denote the public `solve`, `solve?`, and
`inverse?` entry points, including forcing every returned matrix/vector entry
and every inconsistency-witness entry. Successful solve checksums traverse
stored matrix data without evaluating the dependent rank expression again.
The compiled solve and its checksum wrapper together perform one reduction.

| Prefix | Parameter | Fixed parameters | Scientific ladder |
|---|---|---|---|
| `rat8`, `rat32`, `rat128` | dimension n | rational input height 8, 32, 128 respectively | 4, 8, 16, 32, 64 |
| `modular` | dimension n | ZMod64 101 | 4, 8, 16, 32, 64 |
| `functions` | dimension n | RationalFn Rat; degree 1, coefficient height parameter 8 | 2, 4, 8 |
| `height8`, `height16` | coefficient height h | dimension 8, 16 respectively | 8, 16, 32, 64, 128, 256 |

Seed 10222 generates dense `I + u vᵀ` matrices, with repeated rows/columns
for the deficient and rectangular families. Rational entries share a
denominator. Tall inputs are 2n×n and wide inputs are n×2n. Rank and augmented
rank are checked during preparation, outside the timer. The
[input metadata](bench-results/hex-row-reduce-field-inputs-bounded.jsonl) contains all
245 parameter/family combinations, dimensions, rank, input hash, actual
numerator/denominator/RHS bit heights, and rational-function degrees. The generator reserves coefficient headroom before the dense updates; all
actual matrix and RHS entries meet the requested height bound.

Dimension registrations use mode 1: r proportional to n and fixed aspect ratio
make `O(rn(n+m) + n² + m(m−r))` field operations cubic. Rational timings also
include integer arithmetic and coefficient growth; cubic field-operation
counts alone do not assert cubic bit complexity.

Height registrations use mode 2. At a fixed matrix size, intermediate bit
length is O(h), and classical multiplication, division, and GCD give a
quadratic arithmetic upper bound. GMP documents the quadratic bound for
[Lehmer/Euclidean GCD](https://gmplib.org/manual/Lehmer_0027s-Algorithm), the
normalisation phase represented in the profiles below. A tight runtime model
is unavailable across small-integer/GMP representation and arithmetic
thresholds on this short height ladder. Faster observed scaling is assessed
as *within declared upper bound (observed faster)*, separately from the
harness's two-sided verdict; it is not called two-sided consistency.

The field targets use warm child-side repeats, a 200 ms tuning target, three
outer trials in fixed trial-major order, and a 30 s operational per-call cap.
`signalFloorMultiplier := 1.0` uses the exception in
[SPEC/benchmarking.md](../SPEC/benchmarking.md#spawn-floor-filter): the SPEC fixes
these ladders, batches time work inside the child, and this executable's
measured startup floor makes the default 10× filter unusable. Floors and host
load remain in the artifacts. No model, ladder, or cap is changed to obtain a
verdict, and completed samples are never rejected for host activity. The pinned harness
uses smoke parameters 0 and 1; preparation maps these to dimension 2 or height
8, retaining the other family parameters. Verification uses one in-process
call per smoke parameter and does not run the scientific ladder.

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

The original suite contains 12 parametric and 11 fixed targets. Its fixed
repeats agreed and expected hashes matched. Including the field extension,
the compiled suite has 131 parametric and 23 fixed targets. All 154 smoke
checks pass with python-flint 0.9.0; the full `verify` invocation takes 1.50 s
on this host, well below the 30 s per-library warning threshold. The aggregate
repository cap is checked by the existing CI step.

### Field scientific evidence

The [per-registration table](bench-results/hex-row-reduce-fields-verdicts.md)
records each harness verdict, slope, and constant range. It distinguishes
mode-2 upper-bound assessments from two-sided consistency and retains both
observations for every unchanged rerun. Inconclusive dimension evidence is
reported as such.

The source benchmark is commit `9c14175b0`,
with benchmark-file SHA-256
`2cbc832931b6abb022ff3d48a5790077076cde273c1d565cc9dce804f408c0ca`.
The [scientific metadata](bench-results/hex-row-reduce-fields-bounded.meta.json)
records source hashes, exact argv, automatically leased CPU, host, and load.
Measurements use Lean 4.34.0-rc2 on the shared `chungus2` AMD EPYC 9455 host.

```sh
HEX_FLINT_BENCH_PYTHON=/tmp/hexvenv/bin/python \
  python3 scripts/bench/row_reduce_fields.py \
  reports/bench-results/hex-row-reduce-fields-bounded
```

Diagnostic artifacts are retained with prefixes `hex-row-reduce-fields-scientific`
and `hex-row-reduce-fields-comparison`. The former contains all 1,785 completed
warm samples with the default spawn filter; all 119 verdicts are inconclusive.
Its successful-solve checksum evaluates the dependent rank, adding a second
reduction. The latter includes input construction in fixed calls. Neither
collection supplies headline timings. Their source hashes and complete raw
measurements remain available for audit. The bounded collection uses the stored
data checksum and prepared comparison inputs described above. The additional
`fields-final`, `fields-cached`, and `fields-payload` collections retain the
intermediate generator with coefficient heights exceeding its requested
parameter; they are diagnostic evidence only. `fields-hashes` records the
complete-output anchor checks establishing the bounded generator hashes.

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
Rank is the only identical callable result in this original rank comparator. RREF and
nullspace values remain correctness-oracle surfaces, and the other eleven
benchmark targets carry the exact absence tag
`no-comparable-surface-in-named-comparator`.

### Field inverse and unique solve comparisons

The informational comparator **FLINT fmpq_mat.inv()/solve() via python-flint**
returns the complete inverse or the unique square solution with its empty
basis. Both sides consume the same seeded height-32 inputs at dimensions
8, 16, and 32. Lean inputs and JSON request fields are closed prepared
constants; FLINT matrices are cached during warmup. Output extraction and
serialization remain in the timed calls, and every expected hash matches.
General affine solutions and negative witnesses carry
`no-comparable-surface-in-named-comparator`.

Four adjacent blocks alternate AB/BA order on one automatically leased CPU.
The table reports the median of each arm's four block medians. The
[cached comparison metadata](bench-results/hex-row-reduce-fields-bounded-comparison.meta.json)
contains exact commands and source hashes; its per-block JSON files retain
all measurements. Fixed comparisons and protocol anchors have the limited
purpose of output agreement and relative timing, not absolute performance
budgets.

| Operation | Dimension | Lean ms | FLINT ms | Raw Lean / FLINT | Same-payload overhead ms | Overhead / FLINT |
|---|---:|---:|---:|---:|---:|---:|
| inverse | 8 | 0.874 | 0.282 | 3.10× | 0.315 | 111.8% |
| inverse | 16 | 7.586 | 0.924 | 8.21× | 0.819 | 88.6% |
| inverse | 32 | 69.515 | 3.752 | 18.53× | 3.451 | 92.0% |
| solve | 8 | 0.994 | 0.111 | 8.99× | 0.100 | 90.0% |
| solve | 16 | 8.032 | 0.328 | 24.51× | 0.324 | 98.8% |
| solve | 32 | 71.460 | 1.142 | 62.56× | 1.068 | 93.5% |

The raw end-to-end ratio widens across all three dimensions for both
operations. The eligible range for a native-algorithm ratio is empty:
same-payload overhead exceeds the SPEC's 50% limit at every rung. All measured
calls are below the soft one-second ceiling, but that does not fix the
protocol floor. No overhead-adjusted native-kernel speed claim follows.

The constant-size protocol anchor is 15.699 μs. It understates field-call
overhead because field requests/responses contain full matrices. The
[payload calibration](bench-results/hex-row-reduce-fields-bounded-payload.meta.json)
therefore uses `row_reduce_overhead.py` through the existing
`HEX_FLINT_BENCH_DRIVER` hook. It caches only the native inverse/solve result
at warmup, retaining identical request parsing, input-cache lookup, rational
extraction, serialization, transport, and Lean decoding. Its complete output
hashes also match. The inverse-8 overhead observation exceeds the native-call
observation on this shared host; subtraction is unresolved, and both runs are
retained. These are host-specific API/protocol timings.

```sh
HEX_FLINT_BENCH_PYTHON=/tmp/hexvenv/bin/python \
  python3 scripts/bench/row_reduce_fields.py \
  reports/bench-results/hex-row-reduce-fields-bounded-comparison --phase comparisons
HEX_FLINT_BENCH_PYTHON=/tmp/hexvenv/bin/python \
  python3 scripts/bench/row_reduce_fields.py \
  reports/bench-results/hex-row-reduce-fields-bounded-payload --phase overhead
```

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

### Field inverse and solve profile

`field-inverse-solve` is represented by `Field.rat32FullSolve 32`, the
solve surface with the largest raw comparator gap. The
[profile summary](bench-results/hex-row-reduce-fields-profile-bounded.json) and
[command/source metadata](bench-results/hex-row-reduce-fields-profile-bounded.meta.json)
record source, host activity, sampler version, CPU lease, and exact invocation.
The child is pinned to CPU 85; the recorder retains the host affinity mask.
Pinning the recorder itself produced an empty profile, retained locally at
`/tmp/hex-profile-rat32FullSolve-32.json.gz.failed-raw-s27mu93t`.

The postprocessor reports confidence **passed**, a **0.274 ms** calibration
residual, **2325.773 ms** timed duration, **2324 retained / 74 rejected**
samples, **0 off-thread** samples in the window, and a **passed** sensitivity
check. Rejected samples lie outside the benchmark's timed regions.

| Leaf category | Share |
|---|---:|
| GMP arithmetic | 45.14% |
| Allocation/free | 38.34% |
| Lean runtime | 14.85% |
| Lean own code | 0.56% |
| Other | 1.12% |

Inclusive attribution places `Hex.Matrix.solve` at 99.18%, `rowReduce` at 96.04% and
`rowReduceLoop` at 96.00%, `eliminateColumn` at 94.54%, and `rowAdd` at 94.45%.
Matrix-vector multiplication accounts for 3.01%. Rational normalisation and
allocation in dense row operations dominate; extracting the particular
solution and materialising the empty nullspace contribute little on this
full-rank case. This profile covers the registered solve target and the
arithmetic phase used in the height-bound derivation. The earlier diagnostic
[checksum profile](bench-results/hex-row-reduce-fields-profile.json) is retained
separately and does not supply final attribution.

The wrapper used for the final profile executes
`taskset -c 85 .lake/build/bin/hexrowreduce_bench "$@"`; its CPU is chosen by
the same nonblocking lease scheme as the collector, without screening load.
The recorded orchestrator command is reproducible by setting `--bench-exe`
to that child wrapper. Summarise its filtered output with:

```sh
python3 scripts/profile/summarize_profile.py \
  /tmp/hex-profile-rowreduce-fields-bounded.json.gz \
  --thread hexrowreduce_bench \
  --output reports/bench-results/hex-row-reduce-fields-profile-bounded.json
```

## Concerns

The dimension evidence remains inconclusive on the registrations identified
in the linked verdict table; these are not promoted to passing complexity
claims. Small-dimension rational-function rank-n−1 families change rank from
1 to 3 to 7, and coefficient arithmetic also changes with dimension. Modular
small rungs include materialisation/runtime overhead that declines relative
to elimination. Both effects can prevent a tight cubic time fit on the fixed
SPEC ladder even though the field-operation bound is cubic. The one unchanged
rerun is retained alongside the first result; no further retry or ladder/model
change is used to force agreement. Native FLINT timing ratios remain unresolved
because complete-payload overhead dominates. Correctness, smoke verification,
and the documented measurement coverage are independent of these limitations.
