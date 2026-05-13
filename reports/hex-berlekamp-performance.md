# HexBerlekamp Performance Report

## Bench Targets

- `Hex.BerlekampBench.runBerlekampMatrixChecksum`: `n * n`
- `Hex.BerlekampBench.runRabinTestChecksum`: `n * n * n`
- `Hex.BerlekampBench.runBerlekampFactorChecksum`: `n * n`
- `Hex.BerlekampBench.runDistinctDegreeChecksum`: `n * n * n`

## Verdicts

Scientific run at commit `ad74d65a9295` on `carica` (Apple M2 Ultra,
macOS 14.6.1), command:

```sh
lake exe hexberlekamp_bench run \
    Hex.BerlekampBench.runBerlekampMatrixChecksum \
    Hex.BerlekampBench.runRabinTestChecksum \
    Hex.BerlekampBench.runBerlekampFactorChecksum \
    Hex.BerlekampBench.runDistinctDegreeChecksum \
    --export-file reports/bench-results/hex-berlekamp-ad74d65.json
```

The deterministic benchmark fixtures in `HexBerlekamp/Bench.lean` use
the fixed small prime `p = 5`; no random seeds are involved. The harness
recorded `ad74d65-dirty` because this worktree carried a pre-existing
local `.claude/CLAUDE.md` modification outside this evidence package.
Export artefact: `reports/bench-results/hex-berlekamp-ad74d65.json`,
SHA-256 `af9f901e5a8be1f3ae6c6c7313d9dd37f8985179884d880d07de3dc53bb6c9c7`.

- `Hex.BerlekampBench.runBerlekampMatrixChecksum`: consistent with
  declared complexity (`cMin=1560.075, cMax=2374.100, beta=-0.158`,
  parameters `16..192`, final hash `0xa562d3f84baa18e9`).
- `Hex.BerlekampBench.runRabinTestChecksum`: consistent with declared
  complexity (`cMin=1068.124, cMax=1349.340, beta=-0.047`,
  densified ladder `8,10,12,16,20,24,32,40,48,56,64`, final hash `0xd`).
- `Hex.BerlekampBench.runBerlekampFactorChecksum`: consistent with
  declared complexity (`cMin=1828.018, cMax=2634.728, beta=-0.149`,
  parameters `16..256`, final hash `0xf7bf198d9173a6ce`).
- `Hex.BerlekampBench.runDistinctDegreeChecksum`: consistent with
  declared complexity (`cMin=1627.883, cMax=2869.790, beta=-0.296`,
  densified ladder `12,16,20,24,32,40,48,64,80,96`,
  final hash `0x967aa08b9f90679`).

Smoke wiring was checked at the same commit with:

```sh
lake exe hexberlekamp_bench list
lake exe hexberlekamp_bench verify
```

`verify` passed all four registered benchmarks.

## Comparator Ratios

`SPEC/Libraries/hex-berlekamp.md` names two `gating` FLINT comparators:
`nmod_poly.is_irreducible` for `runRabinTestChecksum` and
`nmod_poly.factor_distinct_deg` for `runDistinctDegreeChecksum`. Both
are wired through `Hex.BenchOracle.Flint.runOp` and registered as fixed
per-rung benchmark pairs over the same input families as the Lean
targets.

Measured fixed-comparator process-call overhead is about `52 ms` per
call on this host. The current fixed registrations spawn one benchmark
child per repeat, so even though the FLINT driver is persistent inside
that child, the Python/driver startup dominates the FLINT medians at
every rung below. Raw ratios are `FLINT median / Lean median`; adjusted
ratios subtract `52 ms` from the FLINT median when positive. Because the
overhead is more than 50% of measured FLINT wall time at every rung, no
rung is eligible for a final gating-goal verdict under
`SPEC/benchmarking.md §"Headline reports" §"Comparator ratios"`.

### FLINT `nmod_poly.is_irreducible` vs Rabin

| n | Lean median | FLINT median | raw ratio | adjusted ratio | eligible |
|---:|---:|---:|---:|---:|:---:|
| 8 | 0.777 ms | 53.229 ms | 68.532x | 1.582x | no |
| 10 | 1.486 ms | 54.783 ms | 36.871x | 1.873x | no |
| 12 | 2.114 ms | 52.346 ms | 24.767x | 0.164x | no |
| 16 | 5.312 ms | 55.379 ms | 10.426x | 0.636x | no |
| 20 | 10.554 ms | 51.723 ms | 4.901x | 0.000x | no |
| 24 | 16.019 ms | 57.258 ms | 3.574x | 0.328x | no |
| 32 | 36.021 ms | 69.158 ms | 1.920x | 0.476x | no |
| 40 | 81.167 ms | 55.964 ms | 0.689x | 0.049x | no |
| 48 | 127.045 ms | 55.526 ms | 0.437x | 0.028x | no |
| 56 | 217.878 ms | 53.264 ms | 0.244x | 0.006x | no |
| 64 | 329.806 ms | 53.284 ms | 0.162x | 0.004x | no |

Trend: raw ratios fall monotonically after the small-startup regime;
FLINT is raw-faster by `n = 40` and the gap widens through `n = 64`.
The adjusted ratios are not a valid verdict curve because the overhead
floor dominates every FLINT measurement. Gating-goal verdict:
**blocked/no eligible rung** for this process-call shape.

### FLINT `nmod_poly.factor_distinct_deg` vs DDF

The DDF fixed targets use an opaque timing token for the fixed compare:
the conformance oracle compares monic-normalised degree buckets, while
the raw Lean and FLINT representative checksums are not a stable shared
observable.

| n | Lean median | FLINT median | raw ratio | adjusted ratio | eligible |
|---:|---:|---:|---:|---:|:---:|
| 12 | 5.872 ms | 56.241 ms | 9.578x | 0.722x | no |
| 16 | 11.453 ms | 52.724 ms | 4.604x | 0.063x | no |
| 20 | 18.630 ms | 52.191 ms | 2.801x | 0.010x | no |
| 24 | 38.281 ms | 55.162 ms | 1.441x | 0.083x | no |
| 32 | 69.851 ms | 57.250 ms | 0.820x | 0.075x | no |
| 40 | 117.502 ms | 57.305 ms | 0.488x | 0.045x | no |
| 48 | 214.047 ms | 55.294 ms | 0.258x | 0.015x | no |
| 64 | 509.125 ms | 55.684 ms | 0.109x | 0.007x | no |
| 80 | 882.482 ms | 56.784 ms | 0.064x | 0.005x | no |
| 96 | 1.470 s | 56.130 ms | 0.038x | 0.003x | no |

Trend: raw ratios cross in FLINT's favour by `n = 32` and continue
falling through `n = 96`. As with Rabin, the process-call overhead
dominates every FLINT row, so the adjusted curve is informational only.
Gating-goal verdict: **blocked/no eligible rung** for this process-call
shape.

## Profile

The profiles below were recorded with `samply record --save-only
--unstable-presymbolicate` at commit `e7bf7c23bbb5` on `carica`
(Apple M2 Ultra, macOS 14.6.1) at the default 1 kHz sampling rate.
Raw Firefox Profiler JSON artefacts are developer-local under
`/tmp/hex-profiles/` and are not committed. The optimized macOS build
kept essentially all sampled child time in the generated Lean
registration closure for each target rather than unwinding through
smaller source functions; the attribution review below therefore maps
that closure back to the registered target and the source-level
algorithm path in `HexBerlekamp/Bench.lean` and `HexBerlekamp/*`.
Across the four child profiles, classified leaf samples were at least
99.5% own compiled Lean code, with Lean runtime and allocation/free
each below 0.5%; no GMP big-integer cost was observed, as expected for
fixed-word `ZMod64 5` arithmetic.

### `berlekamp-matrix`

Command:

```sh
lake exe hexberlekamp_bench profile Hex.BerlekampBench.runBerlekampMatrixChecksum \
    --param 192 --target-inner-nanos 5000000000 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        -o /tmp/hex-profiles/hex-berlekamp-matrix-e7bf7c2.json --"
```

Representative case: deterministic monic `F_5` polynomial
`monicPoly 193 101`, parameter `n = 192`, no seed. Child row:
`inner_repeats=64`, `per_call_nanos=62169035.156250`,
`result_hash=0xa562d3f84baa18e9`. Total `4095` main-thread samples.
Leaf classification was own compiled Lean code 99.5%, Lean runtime
0.3%, allocation/free 0.1%, GMP 0.0%, other below 0.1%. Inclusive
cost was led by the optimized registration closure for
`runBerlekampMatrixChecksum` (99.5%). Source attribution maps this
closure to `berlekampMatrix`, whose work is the fixed-prime Frobenius
column recurrence over a degree-`n` dense polynomial. The dominant
work is exactly the registered `runBerlekampMatrixChecksum` target
and matches the declared quadratic model.

### `rabin-irreducibility`

Command:

```sh
lake exe hexberlekamp_bench profile Hex.BerlekampBench.runRabinTestChecksum \
    --param 64 --target-inner-nanos 5000000000 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        -o /tmp/hex-profiles/hex-berlekamp-rabin-e7bf7c2.json --"
```

Representative case: deterministic monic `F_5` polynomial
`monicPoly 65 101`, parameter `n = 64`, no seed. Child row:
`inner_repeats=16`, `per_call_nanos=341168148.437500`,
`result_hash=0xd`. Total `5855` main-thread samples. Leaf
classification was own compiled Lean code 99.6%, Lean runtime 0.3%,
allocation/free below 0.1%, GMP 0.0%, other below 0.1%. Inclusive
cost was led by the optimized registration closure for
`runRabinTestChecksum` (99.6%). Source attribution maps this closure
to `rabinTest`, where the Frobenius remainder and bounded gcd checks
dominate the dense fixed-prime polynomial work. The profiled cost is
covered by the registered `runRabinTestChecksum` target and matches
the declared cubic model.

### `split-step-factorization`

Command:

```sh
lake exe hexberlekamp_bench profile Hex.BerlekampBench.runBerlekampFactorChecksum \
    --param 256 --target-inner-nanos 5000000000 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        -o /tmp/hex-profiles/hex-berlekamp-factor-e7bf7c2.json --"
```

Representative case: Fibonacci-style polynomial pair
`fibPoly 258` and `fibPoly 257`, parameter `n = 256`, no seed.
Child row: `inner_repeats=32`, `per_call_nanos=128112763.000000`,
`result_hash=0xf7bf198d9173a6ce`. Total `4296` main-thread samples.
Leaf classification was own compiled Lean code 99.5%, Lean runtime
0.3%, allocation/free below 0.1%, GMP 0.0%, other below 0.1%.
Inclusive cost was led by the optimized registration closure for
`runBerlekampFactorChecksum` (99.5%). Source attribution maps this
closure to the constant-size sweep of `splitFactorAt` calls, each
performing a dense Euclidean gcd against the prepared witness. The
dominant work is directly measured by the registered target and
matches the declared quadratic fixed-prime model.

### `distinct-degree-factorization`

Command:

```sh
lake exe hexberlekamp_bench profile Hex.BerlekampBench.runDistinctDegreeChecksum \
    --param 96 --target-inner-nanos 5000000000 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        -o /tmp/hex-profiles/hex-berlekamp-ddf-e7bf7c2.json --"
```

Representative case: deterministic monic `F_5` polynomial
`monicPoly 99 211`, parameter `n = 96`, no seed. Child row:
`inner_repeats=2`, `per_call_nanos=1523663271.000000`,
`result_hash=0x967aa08b9f90679`. Total `4642` main-thread samples.
Leaf classification was own compiled Lean code 99.5%, Lean runtime
0.3%, allocation/free below 0.1%, GMP 0.0%, other below 0.1%.
Inclusive cost was led by the optimized registration closure for
`runDistinctDegreeChecksum` (99.5%). Source attribution maps this
closure to `distinctDegreeFactor`, where repeated Frobenius updates
and gcds over the residual dominate. The work is covered by the
registered `runDistinctDegreeChecksum` target and matches the
declared cubic model.

## Concerns

- The two required FLINT gating comparators are wired, but the current
  fixed process-call measurement shape has no eligible rung: driver
  startup is more than 50% of the measured FLINT wall time for both
  surfaces across the full ladder. HexBerlekamp should not re-claim
  Phase 4 until either the comparator harness amortises the persistent
  driver across measured inner repeats or an FFI comparator replaces the
  process-call path.
- The raw FLINT trend is adverse for both gating surfaces: after startup
  stops dominating the Lean side, FLINT is substantially faster by the
  largest measured rung (`0.162x` raw for Rabin at `n = 64`, `0.038x`
  raw for DDF at `n = 96`, where lower is faster for FLINT/Lean ratios).
