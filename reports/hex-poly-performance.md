# HexPoly Performance Report

## Bench Targets

- `Hex.PolyBench.runAddChecksum`: `n`
- `Hex.PolyBench.runSubChecksum`: `n`
- `Hex.PolyBench.runMulChecksum`: `n * n`
- `Hex.PolyBench.runEval`: `n`
- `Hex.PolyBench.runComposeChecksum`: `n * n * n * n`
- `Hex.PolyBench.runDerivativeChecksum`: `n`
- `Hex.PolyBench.runDivModChecksum`: `n * n`
- `Hex.PolyBench.runDivChecksum`: `n * n`
- `Hex.PolyBench.runModChecksum`: `n * n`
- `Hex.PolyBench.runModByMonicChecksum`: `n * n`
- `Hex.PolyBench.runGcdChecksum`: `n * n`
- `Hex.PolyBench.runXGcdChecksum`: `n * n`
- `Hex.PolyBench.runContent`: `n`
- `Hex.PolyBench.runPrimitivePartChecksum`: `n`
- `Hex.PolyBench.runPolyCRTChecksum`: `n * n`

## Verdicts

The parametric verdicts below come from the scientific run at commit
`b9d853c58f9f85c24c451e7f30890a215759a196` on `carica` (Apple M2 Ultra,
macOS 14.6.1). That run included the then-current fixed registrations, but its
fixed timings are superseded by the warmed `e44c4be1e` export in Comparator
Ratios and are not reused here:

```sh
lake exe hexpoly_bench run $(lake exe hexpoly_bench list | awk '/^  Hex\./ {print $1}') \
    --export-file reports/bench-results/hex-poly-b9d853c.json
```

The run used deterministic benchmark inputs from `bench/HexPoly/Bench.lean`; random
seeds are not involved. The harness recorded `b9d853c-dirty` because this
worktree had an unrelated pre-existing `.claude/CLAUDE.md` modification.
Export artefact: `reports/bench-results/hex-poly-b9d853c.json`.

- `Hex.PolyBench.runEval`: consistent with declared complexity (`β=-0.004`,
  parameters `8192..131072`, final hash `0x41cb15d2703fbc8c`).
- `Hex.PolyBench.runDivChecksum`: consistent with declared complexity
  (`β=-0.059`, parameters `64..512`, final hash `0xc61628eb23727403`).
- `Hex.PolyBench.runContent`: consistent with declared complexity
  (`β=+0.001`, parameters `8192..131072`, final hash `0xc`).
- `Hex.PolyBench.runAddChecksum`: consistent with declared complexity
  (`β=-0.008`, parameters `8192..131072`, final hash
  `0xd5b9f2ba6ec00df3`).
- `Hex.PolyBench.runPolyCRTChecksum`: consistent with declared complexity
  (parameters `128..512`, final hash `0x6b2ee9ab30297af7`).
- `Hex.PolyBench.runPrimitivePartChecksum`: consistent with declared
  complexity (`β=+0.010`, parameters `8192..131072`, final hash
  `0x6723bfbfb8236996`).
- `Hex.PolyBench.runGcdChecksum`: consistent with declared complexity
  (`β=-0.069`, parameters `16..96`, final hash `0x1b1bcaf06d8ce2c1`).
- `Hex.PolyBench.runXGcdChecksum`: consistent with declared complexity
  (`β=-0.080`, parameters `16..96`, final hash `0xd7c3a48ff94871b3`).
- `Hex.PolyBench.runDerivativeChecksum`: consistent with declared complexity
  (`β=-0.010`, parameters `8192..131072`, final hash
  `0x136784a3e32917c5`).
- `Hex.PolyBench.runSubChecksum`: consistent with declared complexity
  (`β=-0.001`, parameters `8192..131072`, final hash
  `0xb661ce41e16ecdac`).
- `Hex.PolyBench.runComposeChecksum`: consistent with declared complexity
  (parameters `16..64`, final hash `0x22d4cff389f27388`).
- `Hex.PolyBench.runModByMonicChecksum`: consistent with declared complexity
  (`β=-0.065`, parameters `64..512`, final hash `0xe292fd87a14a5ba4`).
- `Hex.PolyBench.runModChecksum`: consistent with declared complexity
  (`β=-0.054`, parameters `64..512`, final hash `0x9829367400164008`).
- `Hex.PolyBench.runMulChecksum`: consistent with declared complexity
  (parameters `128..512`, final hash `0xd634bb91fcd2a52d`).
- `Hex.PolyBench.runDivModChecksum`: consistent with declared complexity
  (`β=-0.057`, parameters `64..512`, final hash `0x9afda056859428e`).

The repaired `e44c4be1e` comparator export described below contains all 88
paired fixed registrations. Every registration has stable repeat hashes, and
each Lean/FLINT pair returns the same observed hash at every rung.

Smoke wiring was also checked with:

```sh
lake exe hexpoly_bench list
lake exe hexpoly_bench verify
```

`verify` passed all 103 registered benchmarks after the protocol repair (15
parametric + 88 paired fixed comparator rungs).

## Comparator Ratios

`HexPoly/SPEC/hex-poly.md`, §"External comparators", names
FLINT fmpz_poly via python-flint as the informational comparator for the seven
integer-polynomial surfaces below. The non-integer registrations remain outside
that declared scope.

The paired fixed registrations were rerun after the protocol repair at commit
`e44c4be1e80e26a244aeb40a5d01e046ad687ab5` on `chungus2` (AMD EPYC
9455, Linux x86_64), pinned to CPU 6:

```sh
PATH=/tmp/hex-9804-flint/bin:$PATH
lake exe hexpoly_bench list | awk '/\[fixed\]/{print $1}' |
  xargs taskset -c 6 lake exe hexpoly_bench run \
    --export-file reports/bench-results/hex-poly-e44c4be-issue9804-warmed.json
```

The export contains all 88 fixed registrations, 440 successful outer repeats,
and no hash disagreement, either within a registration or between any Hex/FLINT
pair. Its SHA-256 is
`7018a2838fd969bdc16bbcc54746fcc1b653dd889ebf71029df2d613bbdfe9a7`.

### Protocol overhead and eligibility

Each FLINT registration now sets `warmupFirstIter := true`. Its discarded
first call starts python-flint; every timed inner-repeat batch reuses that
process. The paired Hex registration uses the same `minTotalSeconds := 0.2`,
so both sides report per-call medians on the same timing basis.

Fresh one-request processes took 48 ms median over 11 trials. That is startup,
reported separately and excluded by the warmup. A 100000-request
`fmpz_poly.overhead` run took 0.357 s median over five trials, an upper bound
of 3.57 µs per steady-state JSON round trip (it also includes shell-pipeline
cost and amortized startup). The smallest FLINT median below is 128.351 µs, so
protocol overhead is at most 2.8% on every rung. No adjusted ratio is required
by `SPEC/benchmarking.md`'s 5% rule. Every median is also below the ten-second
hard ceiling; all 44 pairs are eligible.

The ratio in every table is `FLINT / Hex`. Values below one mean FLINT is
faster.

### Addition

| n | Hex median | FLINT median | FLINT / Hex | eligible |
|---:|---:|---:|---:|:---:|
| 16384 | 480.868 µs | 15.710 ms | 32.6709x | yes |
| 32768 | 1.055 ms | 14.468 ms | 13.7197x | yes |
| 49152 | 2.333 ms | 42.047 ms | 18.0218x | yes |
| 65536 | 2.125 ms | 107.741 ms | 50.7038x | yes |
| 98304 | 2.946 ms | 85.307 ms | 28.9570x | yes |
| 131072 | 3.891 ms | 57.971 ms | 14.8970x | yes |

Across six eligible rungs the ratio remains above one and fluctuates rather
than moving monotonically; serialization and Python object construction
dominate this coefficientwise kernel. The warmed data supports no adverse
algorithmic trend.

### Subtraction

| n | Hex median | FLINT median | FLINT / Hex | eligible |
|---:|---:|---:|---:|:---:|
| 16384 | 686.232 µs | 6.984 ms | 10.1776x | yes |
| 32768 | 1.715 ms | 15.734 ms | 9.1731x | yes |
| 49152 | 2.027 ms | 21.252 ms | 10.4861x | yes |
| 65536 | 3.317 ms | 29.786 ms | 8.9805x | yes |
| 98304 | 3.168 ms | 43.183 ms | 13.6293x | yes |
| 131072 | 7.037 ms | 57.361 ms | 8.1518x | yes |

The six-rung ratio stays in the 8.15–13.63x band with no directional
divergence. This is the cleanest linear-kernel curve in the repaired run.

### Multiplication

| n | Hex median | FLINT median | FLINT / Hex | eligible |
|---:|---:|---:|---:|:---:|
| 128 | 227.101 µs | 166.407 µs | 0.7327x | yes |
| 192 | 403.768 µs | 128.351 µs | 0.3179x | yes |
| 256 | 675.534 µs | 171.051 µs | 0.2532x | yes |
| 320 | 755.987 µs | 210.524 µs | 0.2785x | yes |
| 384 | 1.550 ms | 458.585 µs | 0.2959x | yes |
| 448 | 1.634 ms | 298.353 µs | 0.1826x | yes |
| 512 | 1.971 ms | 340.564 µs | 0.1728x | yes |

FLINT is already faster at the bottom rung and its ratio falls from 0.733x to
0.173x across the seven-rung ladder. This expected divergence matches the
normative contract: FLINT tunes Karatsuba/Toom-Cook/FFT crossovers while
HexPoly deliberately provides the schoolbook semantic foundation. It is an
informational finding, not a Concern.

### Derivative

| n | Hex median | FLINT median | FLINT / Hex | eligible |
|---:|---:|---:|---:|:---:|
| 16384 | 368.015 µs | 5.224 ms | 14.1938x | yes |
| 32768 | 905.000 µs | 21.939 ms | 24.2425x | yes |
| 49152 | 1.696 ms | 15.751 ms | 9.2846x | yes |
| 65536 | 1.242 ms | 21.159 ms | 17.0407x | yes |
| 98304 | 3.486 ms | 31.609 ms | 9.0669x | yes |
| 131072 | 2.449 ms | 80.256 ms | 32.7662x | yes |

The ratio is noisy but remains above one at all six eligible rungs and has no
monotone adverse shape. The table records the full curve without turning the
noise into an algorithmic claim.

### Composition

| n | Hex median | FLINT median | FLINT / Hex | eligible |
|---:|---:|---:|---:|:---:|
| 16 | 5.239 ms | 2.488 ms | 0.4748x | yes |
| 24 | 17.323 ms | 5.596 ms | 0.3230x | yes |
| 32 | 64.778 ms | 16.332 ms | 0.2521x | yes |
| 40 | 147.036 ms | 61.365 ms | 0.4173x | yes |
| 48 | 539.800 ms | 65.241 ms | 0.1209x | yes |
| 56 | 574.411 ms | 189.326 ms | 0.3296x | yes |
| 64 | 1.021 s | 290.368 ms | 0.2843x | yes |

FLINT is faster throughout. The seven eligible ratios fluctuate inside
0.121–0.475x rather than steadily diverging at the upper end, so this run
supports a stable informational advantage but no adverse trend beyond the
declared downstream specialization boundary.

### Content

| n | Hex median | FLINT median | FLINT / Hex | eligible |
|---:|---:|---:|---:|:---:|
| 16384 | 1.917 ms | 2.876 ms | 1.5003x | yes |
| 32768 | 4.389 ms | 9.369 ms | 2.1344x | yes |
| 49152 | 4.060 ms | 13.913 ms | 3.4266x | yes |
| 65536 | 5.364 ms | 9.788 ms | 1.8248x | yes |
| 98304 | 8.107 ms | 14.592 ms | 1.8000x | yes |
| 131072 | 17.850 ms | 20.373 ms | 1.1414x | yes |

The ratio rises and then returns toward unity; across six eligible rungs there
is no monotone divergence. Hex is faster at every measured input.

### Primitive part

| n | Hex median | FLINT median | FLINT / Hex | eligible |
|---:|---:|---:|---:|:---:|
| 16384 | 2.255 ms | 5.258 ms | 2.3321x | yes |
| 32768 | 2.869 ms | 10.790 ms | 3.7606x | yes |
| 49152 | 4.353 ms | 15.967 ms | 3.6677x | yes |
| 65536 | 5.675 ms | 26.179 ms | 4.6134x | yes |
| 98304 | 8.584 ms | 33.065 ms | 3.8517x | yes |
| 131072 | 11.298 ms | 90.409 ms | 8.0024x | yes |

Hex is faster at all six rungs. The ratio broadly rises, with one mid-ladder
dip, so the direction is favorable to Hex and creates no adverse finding.

## Profile

Profiles were recorded on `carica` (Apple M2 Ultra, macOS 14.6.1,
arm64) from commit `3bc24c50fbe57487776c433106894ee544a6d656`.
The bench binary reported `git_dirty: true` because this worktree had
an unrelated local `.claude/CLAUDE.md` change; the HexPoly sources and
bench executable were built from the commit above. The bench toolchain
was Lean `4.30.0-rc2`, lean-bench `0.1.0`, samply `0.13.1`, and
lean-bench-samply `602da96df3537341b50de9add2f137b0a75a68df`.

Each run used `scripts/profile/run_profile.sh`, which records with
`samply record --save-only --no-open --rate 999
--unstable-presymbolicate` and filters the Firefox Profiler JSON down
to samples on the bench thread inside lean-bench timed regions. The
filtered raw profile artefacts are developer-local under `/tmp` and are
not committed.

### `dense-int-arithmetic`

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexpoly_bench Hex.PolyBench.runComposeChecksum 64 5000000000
```

Representative case: deterministic same-size dense integer composition,
parameter `n = 64`, no seed. Leaf cost after timed-region filtering was
own HexPoly code 64.4%, GMP 17.5%, Lean runtime/harness 7.1%, other
system 5.8%, and allocation/free 5.2%. Inclusive HexPoly cost was led by
`Hex.PolyBench.runComposeChecksum` (99.9%), `DensePoly.compose`'s fold
(98.5%), `DensePoly.mul` (98.1%), and the nested multiplication fold
(93.1%). The dominant work is attributable to the registered dense
composition and multiplication targets.

Diagnostics:

```json
{
  "filtered_profile": "/tmp/hex-profile-runComposeChecksum-64.json.gz",
  "bench_thread": "Thread <4891516>",
  "regions_total": 2,
  "total_timed_ms": 5290.534042,
  "expected_samples_bench_thread": 5285.2,
  "retained_samples_bench_thread": 5283,
  "rejected_samples_bench_thread": 9,
  "off_bench_thread_samples_in_window": 2,
  "samply_interval_ms": 1.001001,
  "spawn_anchor_wall_ns": 1780142588879978000,
  "spawn_anchor_mono_ns": 330622800418208,
  "sidecar_mono_anchor_ns": 330623036488208,
  "samply_meta_start_time_ms": 1780142588887.817
}
```

### `field-euclidean`

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexpoly_bench Hex.PolyBench.runDivModChecksum 512 5000000000
```

Representative case: deterministic fixed-size `F7` division inputs,
parameter `n = 512`, no seed. Leaf cost after timed-region filtering was
own HexPoly code 43.7%, Lean runtime/harness 38.2%, allocation/free
16.3%, and other system 1.7%. Inclusive HexPoly cost was led by
`DensePoly.divMod` and `Hex.PolyBench.runDivModChecksum` (both 100.0%),
`DensePoly.divModArray` (99.2%), and `DensePoly.divModArrayAux` entries
(37.4%, 32.2%, 22.3%). The dominant work maps to the registered division
and remainder targets.

Diagnostics:

```json
{
  "filtered_profile": "/tmp/hex-profile-runDivModChecksum-512.json.gz",
  "bench_thread": "Thread <4892732>",
  "regions_total": 4,
  "total_timed_ms": 3569.440041,
  "expected_samples_bench_thread": 3565.9,
  "retained_samples_bench_thread": 3566,
  "rejected_samples_bench_thread": 8,
  "off_bench_thread_samples_in_window": 2,
  "samply_interval_ms": 1.001001,
  "spawn_anchor_wall_ns": 1780142599690365000,
  "spawn_anchor_mono_ns": 330633610922375,
  "sidecar_mono_anchor_ns": 330633825883625,
  "samply_meta_start_time_ms": 1780142599696.5671
}
```

### `integer-content`

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexpoly_bench Hex.PolyBench.runPrimitivePartChecksum 131072 5000000000
```

Representative case: deterministic dense integer polynomials with nontrivial
content, parameter `n = 131072`, no seed. Leaf cost after timed-region
filtering was own HexPoly code 52.8%, GMP 19.3%, Lean runtime/harness
15.6%, allocation/free 7.0%, and other system 5.2%. Inclusive HexPoly
cost was led by `DensePoly.primitivePart` (70.4%) and the `contentNat`
fold (67.9%). The GMP leaves are expected for integer gcd/content
normalization and are attributable to the registered content and
primitive-part targets.

Diagnostics:

```json
{
  "filtered_profile": "/tmp/hex-profile-runPrimitivePartChecksum-131072.json.gz",
  "bench_thread": "Thread <4893655>",
  "regions_total": 2,
  "total_timed_ms": 3208.018334,
  "expected_samples_bench_thread": 3204.8,
  "retained_samples_bench_thread": 3184,
  "rejected_samples_bench_thread": 16,
  "off_bench_thread_samples_in_window": 1,
  "samply_interval_ms": 1.001001,
  "spawn_anchor_wall_ns": 1780142607741348000,
  "spawn_anchor_mono_ns": 330641661994541,
  "sidecar_mono_anchor_ns": 330641892029416,
  "samply_meta_start_time_ms": 1780142607747.37
}
```

### `polynomial-crt`

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexpoly_bench Hex.PolyBench.runPolyCRTChecksum 512 5000000000
```

Representative case: deterministic coprime monic rational-polynomial moduli,
parameter `n = 512`, no seed. Leaf cost after timed-region filtering was
own HexPoly code 62.1%, GMP 21.9%, Lean runtime/harness 6.8%, other
system 6.3%, and allocation/free 2.9%. Inclusive HexPoly cost was led by
`Hex.PolyBench.runPolyCRTChecksum` (100.0%), `DensePoly.mul` under
`DensePoly.polyCRT` (99.8%), the nested multiplication fold (97.3%),
and `DensePoly.polyCRT` (50.1%, 49.5% call-site entries). The dominant
GMP and multiplication leaves are attributable to the registered CRT
witness construction target.

Diagnostics:

```json
{
  "filtered_profile": "/tmp/hex-profile-runPolyCRTChecksum-512.json.gz",
  "bench_thread": "Thread <4894641>",
  "regions_total": 2,
  "total_timed_ms": 3524.854084,
  "expected_samples_bench_thread": 3521.3,
  "retained_samples_bench_thread": 3518,
  "rejected_samples_bench_thread": 10,
  "off_bench_thread_samples_in_window": 0,
  "samply_interval_ms": 1.001001,
  "spawn_anchor_wall_ns": 1780142615977912000,
  "spawn_anchor_mono_ns": 330649898648500,
  "sidecar_mono_anchor_ns": 330650119680708,
  "samply_meta_start_time_ms": 1780142615985.5298
}
```

No newly dominant inclusive cost in these filtered profiles is
unattributable to a registered bench target, so no audit-found follow-up
was filed from this rerun.

## Concerns
