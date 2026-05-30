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

Scientific run at commit `b9d853c58f9f85c24c451e7f30890a215759a196` on
`carica` (Apple M2 Ultra, macOS 14.6.1), running every registered
parametric target plus every paired Lean/FLINT fixed comparator rung:

```sh
lake exe hexpoly_bench run $(lake exe hexpoly_bench list | awk '/^  Hex\./ {print $1}') \
    --export-file reports/bench-results/hex-poly-b9d853c.json
```

The run used deterministic benchmark inputs from `HexPoly/Bench.lean`; random
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

The 88 paired Lean / FLINT fixed-comparator registrations also passed —
each Lean target and its paired FLINT call returned the same observed
hash at every rung (every `setup_fixed_benchmark` pair appears as a
`"hashes_agree": true` entry in the export).

Smoke wiring was also checked with:

```sh
lake exe hexpoly_bench list
lake exe hexpoly_bench verify
```

`verify` passed all 103 registered benchmarks at the same commit (15
parametric + 88 paired fixed comparator rungs).

## Comparator Ratios

`SPEC/Libraries/hex-poly.md §"External comparators"` names
`FLINT fmpz_poly via python-flint` (matching
`libraries.yml: HexPoly.phase4.comparators[0].tool`) as the
`informational` external comparator for HexPoly, scoped to every
`setup_benchmark` registration on integer polynomial inputs. The comparator is wired through
`Hex.BenchOracle.Flint.runOp` against the shared persistent-subprocess
python-flint driver (`scripts/oracle/flint_bench_driver.py`, HO-20),
which the bench module extends with `fmpz_poly` ops `sub`,
`derivative`, `compose`, `content`, and `primitive_part` to cover
every Hex target on `DensePoly Int`. The seven `setup_benchmark`
registrations over `DensePoly Int`, paired one-to-one with their
FLINT comparator, are: `runAddChecksum` ↔ `fmpz_poly.add`,
`runSubChecksum` ↔ `fmpz_poly.sub`, `runMulChecksum` ↔
`fmpz_poly.mul`, `runDerivativeChecksum` ↔ `fmpz_poly.derivative`,
`runComposeChecksum` ↔ `fmpz_poly.compose`, `runContent` ↔
`fmpz_poly.content`, `runPrimitivePartChecksum` ↔
`fmpz_poly.primitive_part`. The remaining `setup_benchmark`
registrations (`runEval`, the `F7` Euclidean targets
`runDivChecksum`/`runModChecksum`/`runDivModChecksum`/`runModByMonicChecksum`/`runGcdChecksum`/`runXGcdChecksum`,
and `runPolyCRTChecksum` over `Rat`) are not on integer polynomial
inputs and so have no `fmpz_poly` pairing per the SPEC scope.

### Per-call overhead

FLINT per-call overhead is measured by timing one driver spawn plus
one trivial `fmpz_poly.add` request (`/tmp/flint-overhead-measure.py`,
11 spawns on the same host): median **56.3 ms**, min 54.3 ms. The
`setup_fixed_benchmark` shape spawns one bench child per repeat, so
every FLINT median below includes one driver startup. The `adjusted
ratio` column subtracts this overhead from the FLINT median when
positive, then divides by the Lean median. A rung is **eligible**
under `SPEC/benchmarking.md §"Headline reports" §"Comparator ratios"`
when (a) the 56.3 ms overhead is at most 50% of measured FLINT wall
time on that rung and (b) per-call wall time is at most the 10 s hard
ceiling.

### FLINT `fmpz_poly.add` vs `runAddChecksum`

Input family `dense-int-arithmetic`, declared complexity `n`.

| n | Hex median | FLINT median | raw ratio | adjusted ratio | eligible |
|---:|---:|---:|---:|---:|:---:|
| 16384 | 1.992 ms | 67.537 ms | 33.911x | 5.642x | no |
| 32768 | 4.018 ms | 77.961 ms | 19.405x | 5.391x | no |
| 49152 | 5.914 ms | 89.435 ms | 15.123x | 5.603x | no |
| 65536 | 7.898 ms | 101.139 ms | 12.805x | 5.677x | no |
| 98304 | 11.899 ms | 128.186 ms | 10.772x | 6.041x | yes |
| 131072 | 15.897 ms | 153.137 ms | 9.633x | 6.091x | yes |

Trend: raw ratios fall monotonically as `n` grows out of the startup
regime. The two eligible rungs at the top of the ladder give a flat
adjusted ratio around 6x — once driver startup is subtracted, FLINT
spends about six times the wall time Hex does on this surface.

### FLINT `fmpz_poly.sub` vs `runSubChecksum`

Input family `dense-int-arithmetic`, declared complexity `n`.

| n | Hex median | FLINT median | raw ratio | adjusted ratio | eligible |
|---:|---:|---:|---:|---:|:---:|
| 16384 | 2.014 ms | 67.557 ms | 33.546x | 5.590x | no |
| 32768 | 3.936 ms | 81.349 ms | 20.669x | 6.364x | no |
| 49152 | 6.027 ms | 89.602 ms | 14.866x | 5.525x | no |
| 65536 | 7.989 ms | 101.239 ms | 12.672x | 5.625x | no |
| 98304 | 11.815 ms | 124.824 ms | 10.565x | 5.800x | yes |
| 131072 | 15.737 ms | 146.586 ms | 9.315x | 5.737x | yes |

Trend: same shape as `add`. Adjusted ratio is flat around 5.7x at the
eligible rungs.

### FLINT `fmpz_poly.mul` vs `runMulChecksum`

Input family `dense-int-arithmetic`, declared complexity `n²`
(Hex schoolbook against FLINT's Karatsuba / Toom-Cook / FFT crossover).

| n | Hex median | FLINT median | raw ratio | adjusted ratio | eligible |
|---:|---:|---:|---:|---:|:---:|
| 128 | 239.7 µs | 54.253 ms | 226.382x | 0.0000x | no |
| 192 | 537.9 µs | 55.806 ms | 103.742x | 0.0000x | no |
| 256 | 931.2 µs | 56.402 ms | 60.567x | 0.109x | no |
| 320 | 1.431 ms | 57.596 ms | 40.251x | 0.906x | no |
| 384 | 2.117 ms | 54.737 ms | 25.854x | 0.0000x | no |
| 448 | 2.800 ms | 56.092 ms | 20.033x | 0.0000x | no |
| 512 | 3.676 ms | 56.152 ms | 15.277x | 0.0000x | no |

No rung is eligible: at every measured `n`, FLINT's wall time is at or
near the driver-spawn floor of ~55 ms and the per-call overhead is
more than 50% of it. The raw ratio columns mostly read the process
floor, not the algorithm. The adjusted ratios collapse to zero
because FLINT's algorithmic time is below the measurement floor at
this density. This is the canonical
`SPEC/benchmarking.md §"Comparator process overhead reported as
algorithmic difference"` anti-pattern, recorded here in adjusted form
rather than as a raw verdict; the comparator is `informational`, so
no gating-goal verdict is required.

### FLINT `fmpz_poly.derivative` vs `runDerivativeChecksum`

Input family `dense-int-arithmetic`, declared complexity `n`.

| n | Hex median | FLINT median | raw ratio | adjusted ratio | eligible |
|---:|---:|---:|---:|---:|:---:|
| 16384 | 1.410 ms | 63.807 ms | 45.239x | 5.323x | no |
| 32768 | 2.762 ms | 73.346 ms | 26.559x | 6.173x | no |
| 49152 | 4.063 ms | 82.717 ms | 20.358x | 6.502x | no |
| 65536 | 5.541 ms | 88.172 ms | 15.914x | 5.753x | no |
| 98304 | 8.075 ms | 107.214 ms | 13.278x | 6.305x | no |
| 131072 | 10.743 ms | 125.912 ms | 11.721x | 6.480x | yes |

Trend: only the top rung is eligible (the rest sit too close to the
driver-startup floor). The adjusted ratio is flat around 6x once the
overhead is subtracted, similar to `add`/`sub`.

### FLINT `fmpz_poly.compose` vs `runComposeChecksum`

Input family `dense-int-arithmetic`, declared complexity `n⁴`
(Hex Horner-with-schoolbook composition against FLINT's polynomial
composition).

| n | Hex median | FLINT median | raw ratio | adjusted ratio | eligible |
|---:|---:|---:|---:|---:|:---:|
| 16 | 5.034 ms | 56.853 ms | 11.295x | 0.110x | no |
| 24 | 30.248 ms | 68.008 ms | 2.248x | 0.387x | no |
| 32 | 95.952 ms | 84.457 ms | 0.880x | 0.293x | no |
| 40 | 242.261 ms | 122.425 ms | 0.505x | 0.273x | yes |
| 48 | 506.532 ms | 165.324 ms | 0.326x | 0.215x | yes |
| 56 | 941.424 ms | 245.755 ms | 0.261x | 0.201x | yes |
| 64 | 1.645 s | 346.081 ms | 0.210x | 0.176x | yes |

Trend: FLINT pulls steadily ahead — raw ratio falls from 0.505x at the
bottom eligible rung to 0.210x at the top, and the adjusted ratio
follows the same monotone decline. Hex's `compose` uses Horner with
schoolbook multiplication (`O(n⁴)` at the same dense composition
inputs); FLINT composes via its own composition kernel and runs over
ten times faster at `n = 64` (1.6 s vs 346 ms). This adverse trend
is filed as the first Concern below — it does not change the
`informational` classification, but it is the kind of structural gap
the SPEC's `informational` rationale ("Hex schoolbook with declared
Karatsuba crossover; FLINT FFT/Newton-style") was written to flag.

### FLINT `fmpz_poly.content` vs `runContent`

Input family `integer-content`, declared complexity `n`.

| n | Hex median | FLINT median | raw ratio | adjusted ratio | eligible |
|---:|---:|---:|---:|---:|:---:|
| 16384 | 2.992 ms | 59.236 ms | 19.796x | 0.981x | no |
| 32768 | 5.787 ms | 63.267 ms | 10.932x | 1.204x | no |
| 49152 | 8.961 ms | 70.187 ms | 7.832x | 1.550x | no |
| 65536 | 11.687 ms | 72.602 ms | 6.212x | 1.395x | no |
| 98304 | 17.792 ms | 81.817 ms | 4.599x | 1.434x | no |
| 131072 | 24.146 ms | 89.923 ms | 3.724x | 1.393x | no |

Trend: no eligible rung — FLINT wall time stays near the startup floor
at every measured `n`. The adjusted ratio is flat around 1.4x (FLINT
slightly slower than Hex on the algorithmic component), but with
overhead this large compared to the algorithmic time the comparison
is informational only.

### FLINT `fmpz_poly.primitive_part` vs `runPrimitivePartChecksum`

Input family `integer-content`, declared complexity `n`.

| n | Hex median | FLINT median | raw ratio | adjusted ratio | eligible |
|---:|---:|---:|---:|---:|:---:|
| 16384 | 3.724 ms | 64.655 ms | 17.360x | 2.243x | no |
| 32768 | 7.209 ms | 73.646 ms | 10.216x | 2.406x | no |
| 49152 | 10.857 ms | 80.647 ms | 7.428x | 2.243x | no |
| 65536 | 14.475 ms | 90.605 ms | 6.259x | 2.370x | no |
| 98304 | 21.528 ms | 106.981 ms | 4.969x | 2.354x | no |
| 131072 | 28.949 ms | 124.305 ms | 4.294x | 2.349x | yes |

Trend: only the top rung is eligible. Adjusted ratio is flat around
2.3x — FLINT's primitive-part path (content + integer division) takes
roughly twice the wall time Hex does once startup is subtracted.

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

- The FLINT `fmpz_poly.compose` comparator pulls steadily ahead of
  `runComposeChecksum` across the eligible range: raw ratio
  `0.505x → 0.210x` from `n = 40` to `n = 64`, adjusted ratio
  `0.273x → 0.176x`. This is an adverse trend at the `n⁴` composition
  surface. The comparator is `informational`, so this is recorded for
  orientation rather than as a Phase-4 gate; the structural gap
  matches `SPEC/Libraries/hex-poly.md §"External comparators"`'s
  rationale (Hex schoolbook with declared Karatsuba crossover; FLINT
  uses better-asymptotic composition kernels). A follow-up may file a
  narrow HO against `DensePoly.compose` if a faster Hex composition
  surface is wanted.
- The `setup_fixed_benchmark` shape respawns the bench child per
  repeat, so the FLINT median always includes one ~56 ms driver
  startup. For the O(n²) `runMulChecksum` ladder this means no rung
  is currently eligible — FLINT wall time sits near the startup floor
  at every measured `n` and the adjusted ratios collapse to the
  measurement floor. The headline ratios for `mul` are therefore
  informational only; closing this gap would require either
  amortising the persistent driver across measured inner repeats or
  switching `fmpz_poly` to an FFI shim. Tracked here per
  `SPEC/benchmarking.md §"Comparator process overhead reported as
  algorithmic difference"`.
