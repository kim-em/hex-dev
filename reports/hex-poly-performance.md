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
fixed timings are superseded by the warmed `df1870458` export in Comparator
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

The repaired `df1870458` comparator export described below contains all 88
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
`df1870458a39ee328f054b5022721529f27ad1b4` on `chungus2` (AMD EPYC
9455, Linux x86_64), pinned to CPU 6:

```sh
PATH=/tmp/hex-9804-flint/bin:$PATH
lake exe hexpoly_bench list | awk '/\[fixed\]/{print $1}' |
  xargs taskset -c 6 lake exe hexpoly_bench run \
    --export-file reports/bench-results/hex-poly-df18704-issue9804-warmed.json
```

The export contains all 88 fixed registrations, 440 successful outer repeats,
and no hash disagreement, either within a registration or between any Hex/FLINT
pair. Its SHA-256 is
`28d1a79c2bdd58cba745350265564bab1eb0310cdaba39c7fd5d728ec9f5f96d`.

### Protocol overhead and eligibility

Both registrations in every Hex/FLINT pair set `warmupFirstIter := true` and
`minTotalSeconds := 0.2`. The discarded FLINT call starts python-flint; every
timed inner-repeat batch then reuses that process. Warming both arms also keeps
the harness treatment identical, so both sides report per-call medians on the
same timing basis.

Fresh one-request processes took 48 ms median over 11 trials. That is startup,
reported separately and excluded by the warmup. A 100000-request
`fmpz_poly.overhead` run took 0.357 s median over five trials, an upper bound
of 3.57 µs per steady-state JSON round trip (it also includes shell-pipeline
cost and amortized startup). The smallest FLINT median below is 175.870 µs, so
protocol overhead is at most 2.1% on every rung. No adjusted ratio is required
by `SPEC/benchmarking.md`'s 5% rule. Every median is also below the ten-second
hard ceiling; all 44 pairs are eligible.

The ratio in every table is `FLINT / Hex`. Values below one mean FLINT is
faster.

### Addition

| n | Hex median | FLINT median | FLINT / Hex | eligible |
|---:|---:|---:|---:|:---:|
| 16384 | 849.444 µs | 13.718 ms | 16.1499x | yes |
| 32768 | 1.661 ms | 42.796 ms | 25.7699x | yes |
| 49152 | 2.615 ms | 42.909 ms | 16.4075x | yes |
| 65536 | 3.562 ms | 69.756 ms | 19.5853x | yes |
| 98304 | 5.246 ms | 87.558 ms | 16.6916x | yes |
| 131072 | 6.678 ms | 114.503 ms | 17.1456x | yes |

Across six eligible rungs the ratio remains above one in a 16.15–25.77x band
and does not grow with input size. Serialization and Python object construction
dominate this coefficientwise kernel; the warmed data supports no adverse
algorithmic trend.

### Subtraction

| n | Hex median | FLINT median | FLINT / Hex | eligible |
|---:|---:|---:|---:|:---:|
| 16384 | 892.424 µs | 14.566 ms | 16.3214x | yes |
| 32768 | 1.756 ms | 29.985 ms | 17.0787x | yes |
| 49152 | 2.609 ms | 44.201 ms | 16.9396x | yes |
| 65536 | 3.717 ms | 63.784 ms | 17.1590x | yes |
| 98304 | 5.792 ms | 86.193 ms | 14.8802x | yes |
| 131072 | 7.165 ms | 126.389 ms | 17.6393x | yes |

The six-rung ratio stays in the 14.88–17.64x band with no directional
divergence. This is the cleanest linear-kernel curve in the repaired run.

### Multiplication

| n | Hex median | FLINT median | FLINT / Hex | eligible |
|---:|---:|---:|---:|:---:|
| 128 | 239.292 µs | 175.870 µs | 0.7350x | yes |
| 192 | 549.693 µs | 237.844 µs | 0.4327x | yes |
| 256 | 907.721 µs | 332.592 µs | 0.3664x | yes |
| 320 | 1.438 ms | 409.964 µs | 0.2852x | yes |
| 384 | 2.023 ms | 487.665 µs | 0.2410x | yes |
| 448 | 3.007 ms | 591.334 µs | 0.1967x | yes |
| 512 | 3.654 ms | 684.480 µs | 0.1873x | yes |

FLINT is already faster at the bottom rung and its ratio falls from 0.735x to
0.187x across the seven-rung ladder. This expected divergence matches the
normative contract: FLINT tunes Karatsuba/Toom-Cook/FFT crossovers while
HexPoly deliberately provides the schoolbook semantic foundation. It is an
informational finding, not a Concern.

### Derivative

| n | Hex median | FLINT median | FLINT / Hex | eligible |
|---:|---:|---:|---:|:---:|
| 16384 | 550.968 µs | 13.265 ms | 24.0756x | yes |
| 32768 | 1.132 ms | 21.520 ms | 19.0055x | yes |
| 49152 | 1.698 ms | 32.886 ms | 19.3659x | yes |
| 65536 | 2.280 ms | 53.338 ms | 23.3952x | yes |
| 98304 | 3.394 ms | 78.023 ms | 22.9913x | yes |
| 131072 | 4.480 ms | 104.218 ms | 23.2653x | yes |

The ratio remains above one in a 19.01–24.08x band at all six eligible rungs
and has no monotone adverse shape.

### Composition

| n | Hex median | FLINT median | FLINT / Hex | eligible |
|---:|---:|---:|---:|:---:|
| 16 | 5.532 ms | 2.578 ms | 0.4661x | yes |
| 24 | 29.230 ms | 10.340 ms | 0.3537x | yes |
| 32 | 100.891 ms | 30.016 ms | 0.2975x | yes |
| 40 | 263.250 ms | 62.951 ms | 0.2391x | yes |
| 48 | 538.001 ms | 117.141 ms | 0.2177x | yes |
| 56 | 1.040 s | 192.114 ms | 0.1847x | yes |
| 64 | 1.874 s | 299.471 ms | 0.1598x | yes |

FLINT is faster throughout and the seven eligible ratios fall from 0.466x to
0.160x. This expected divergence is an informational result within the
declared downstream-specialization boundary, not a Concern.

### Content

| n | Hex median | FLINT median | FLINT / Hex | eligible |
|---:|---:|---:|---:|:---:|
| 16384 | 2.339 ms | 4.964 ms | 2.1221x | yes |
| 32768 | 4.645 ms | 9.988 ms | 2.1503x | yes |
| 49152 | 6.968 ms | 14.565 ms | 2.0902x | yes |
| 65536 | 9.571 ms | 19.603 ms | 2.0482x | yes |
| 98304 | 13.983 ms | 29.551 ms | 2.1133x | yes |
| 131072 | 17.804 ms | 46.344 ms | 2.6030x | yes |

The ratio stays in a 2.05–2.60x band across six eligible rungs. Hex is faster
at every measured input, with no adverse trend.

### Primitive part

| n | Hex median | FLINT median | FLINT / Hex | eligible |
|---:|---:|---:|---:|:---:|
| 16384 | 2.427 ms | 11.569 ms | 4.7668x | yes |
| 32768 | 4.721 ms | 22.346 ms | 4.7332x | yes |
| 49152 | 7.272 ms | 30.779 ms | 4.2328x | yes |
| 65536 | 9.322 ms | 43.432 ms | 4.6590x | yes |
| 98304 | 14.719 ms | 68.595 ms | 4.6603x | yes |
| 131072 | 18.834 ms | 101.850 ms | 5.4077x | yes |

Hex is faster at all six rungs. The ratio stays in a 4.23–5.41x band, so the
direction is favorable to Hex and creates no adverse finding.

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
