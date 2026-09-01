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
fixed timings are superseded by the warmed `f4f013c63` export in Comparator
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

The repaired `f4f013c63` comparator export described below contains all 88
paired registrations plus the steady-state overhead registration. Every
registration has stable repeat hashes, and
each Lean/FLINT pair returns the same observed hash at every rung.

Smoke wiring was also checked with:

```sh
lake exe hexpoly_bench list
lake exe hexpoly_bench verify
```

`verify` passed all 104 registered benchmarks after the protocol repair (15
parametric + 88 paired fixed comparator rungs + one protocol-overhead case).

## Comparator Ratios

`HexPoly/SPEC/hex-poly.md`, §"External comparators", names
FLINT fmpz_poly via python-flint as the informational comparator for the seven
integer-polynomial surfaces below. The non-integer registrations remain outside
that declared scope.

The paired fixed registrations were rerun after the protocol repair at clean
commit `f4f013c638460c621728e108c9b77988df8d2836` on `chungus2` (AMD
EPYC 9455, Linux x86_64), pinned to CPU 1:

```sh
PATH=/tmp/hex-9804-flint/bin:$PATH
lake exe hexpoly_bench list | awk '/\[fixed\]/{print $1}' |
  xargs taskset -c 1 lake exe hexpoly_bench run \
    --export-file reports/bench-results/hex-poly-f4f013c-issue9804-warmed.json
```

The export contains all 89 fixed registrations, 445 successful outer repeats,
and no hash disagreement, either within a registration or between any Hex/FLINT
pair. Its SHA-256 is
`bed44804f48d11df6508d3ba6ced2b92c864e52fcc888c4a9683704a0a370896`.

### Protocol overhead and eligibility

Both registrations in every Hex/FLINT pair set `warmupFirstIter := true` and
`minTotalSeconds := 0.2`, and fixture preparation is outside the timed closure.
The discarded FLINT call starts python-flint; every timed inner-repeat batch
then reuses that process. Startup is therefore represented only by the
discarded warmup and is not folded into the per-call overhead.

The registered synchronous `runFlintOverhead` case measures a steady-state
trivial `fmpz_poly` request through the same persistent driver at 6.178 µs.
This is 7.0% of the smallest FLINT median, so the multiplication `n = 128` row
also reports the overhead-adjusted ratio required by `SPEC/benchmarking.md`.
The overhead is below 50% of every comparator median, and every median is below
the ten-second hard ceiling, so all 44 pairs are eligible.

The ratio in every table is `FLINT / Hex`. Values below one mean FLINT is
faster.

### Addition

| n | Hex median | FLINT median | FLINT / Hex | eligible |
|---:|---:|---:|---:|:---:|
| 16384 | 515.304 µs | 6.934 ms | 13.457x | yes |
| 32768 | 1.011 ms | 14.212 ms | 14.060x | yes |
| 49152 | 1.530 ms | 21.175 ms | 13.837x | yes |
| 65536 | 2.077 ms | 28.445 ms | 13.698x | yes |
| 98304 | 3.026 ms | 42.657 ms | 14.096x | yes |
| 131072 | 4.158 ms | 59.036 ms | 14.198x | yes |

Across six eligible rungs the end-to-end ratio stays in a narrow 13.46–14.20x
band. Hex encoding, JSON framing, and Python object construction materially
contribute to this linear comparator surface, so these ratios characterize the
declared process-call protocol rather than isolated addition kernels.

### Subtraction

| n | Hex median | FLINT median | FLINT / Hex | eligible |
|---:|---:|---:|---:|:---:|
| 16384 | 517.977 µs | 7.590 ms | 14.653x | yes |
| 32768 | 1.003 ms | 16.445 ms | 16.394x | yes |
| 49152 | 1.566 ms | 30.323 ms | 19.359x | yes |
| 65536 | 2.052 ms | 29.067 ms | 14.167x | yes |
| 98304 | 3.105 ms | 44.225 ms | 14.241x | yes |
| 131072 | 4.101 ms | 59.198 ms | 14.434x | yes |

The six-rung end-to-end ratio stays in a 14.17–19.36x band without sustained
growth. As for addition, serialization and object construction prevent a claim
about the isolated subtraction kernels.

### Multiplication

| n | Hex median | FLINT median | FLINT / Hex | adjusted | eligible |
|---:|---:|---:|---:|---:|:---:|
| 128 | 129.271 µs | 88.029 µs | 0.681x | 0.633x | yes |
| 192 | 276.046 µs | 139.425 µs | 0.505x | — | yes |
| 256 | 504.299 µs | 175.638 µs | 0.348x | — | yes |
| 320 | 789.907 µs | 217.740 µs | 0.276x | — | yes |
| 384 | 1.088 ms | 248.783 µs | 0.229x | — | yes |
| 448 | 1.745 ms | 291.683 µs | 0.167x | — | yes |
| 512 | 1.910 ms | 349.189 µs | 0.183x | — | yes |

The ratio falls overall from 0.681x to 0.183x across the seven-rung ladder.
This expected divergence matches the
normative contract: FLINT tunes Karatsuba/Toom-Cook/FFT crossovers while
HexPoly deliberately provides the schoolbook semantic foundation. It is an
informational finding, not a Concern.

### Derivative

| n | Hex median | FLINT median | FLINT / Hex | eligible |
|---:|---:|---:|---:|:---:|
| 16384 | 315.063 µs | 5.405 ms | 17.156x | yes |
| 32768 | 634.103 µs | 10.203 ms | 16.091x | yes |
| 49152 | 953.395 µs | 18.344 ms | 19.241x | yes |
| 65536 | 1.313 ms | 22.443 ms | 17.089x | yes |
| 98304 | 1.943 ms | 32.648 ms | 16.801x | yes |
| 131072 | 3.898 ms | 41.994 ms | 10.772x | yes |

The end-to-end ratio is 10.77–19.24x across the six rungs. This linear surface
is likewise protocol/serialization-sensitive and does not isolate derivative
kernel performance.

### Composition

| n | Hex median | FLINT median | FLINT / Hex | eligible |
|---:|---:|---:|---:|:---:|
| 16 | 3.186 ms | 1.406 ms | 0.441x | yes |
| 24 | 17.601 ms | 5.972 ms | 0.339x | yes |
| 32 | 78.624 ms | 16.431 ms | 0.209x | yes |
| 40 | 144.243 ms | 35.426 ms | 0.246x | yes |
| 48 | 304.027 ms | 68.403 ms | 0.225x | yes |
| 56 | 634.919 ms | 104.885 ms | 0.165x | yes |
| 64 | 1.020 s | 163.363 ms | 0.160x | yes |

The seven eligible ratios fall overall from 0.441x to 0.160x. This expected
divergence is an informational result within the
declared downstream-specialization boundary, not a Concern.

### Content

| n | Hex median | FLINT median | FLINT / Hex | eligible |
|---:|---:|---:|---:|:---:|
| 16384 | 1.355 ms | 2.469 ms | 1.822x | yes |
| 32768 | 2.682 ms | 4.898 ms | 1.827x | yes |
| 49152 | 4.100 ms | 7.366 ms | 1.797x | yes |
| 65536 | 5.378 ms | 18.365 ms | 3.415x | yes |
| 98304 | 8.152 ms | 14.998 ms | 1.840x | yes |
| 131072 | 10.708 ms | 20.543 ms | 1.918x | yes |

The end-to-end ratio is 1.80–3.42x across the six rungs. Coefficient framing
and Python construction are part of this declared process-call surface, so the
table does not support an isolated content-kernel comparison.

### Primitive part

| n | Hex median | FLINT median | FLINT / Hex | eligible |
|---:|---:|---:|---:|:---:|
| 16384 | 1.458 ms | 5.731 ms | 3.930x | yes |
| 32768 | 2.874 ms | 11.203 ms | 3.899x | yes |
| 49152 | 4.299 ms | 17.555 ms | 4.084x | yes |
| 65536 | 5.699 ms | 21.812 ms | 3.827x | yes |
| 98304 | 8.556 ms | 34.340 ms | 4.014x | yes |
| 131072 | 11.309 ms | 42.363 ms | 3.746x | yes |

The end-to-end ratio stays in a 3.75–4.08x band. Because the FLINT arm includes
the declared process-call framing, this is protocol evidence and not a claim
that Hex's primitive-part kernel is intrinsically faster.

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
