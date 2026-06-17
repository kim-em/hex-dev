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

Measurement shape. The fixed FLINT registrations now use
`flintCompareConfig` (`HexBerlekamp/Bench.lean`): `warmupFirstIter :=
true` runs one discarded call so the persistent python-flint driver is
spawned out of the timed region, and `minTotalSeconds := 0.2` forces the
child auto-tuner to amortise steady-state FLINT work across enough inner
repeats that the per-call median reflects the algorithm, not the one-time
process startup. The paired Lean targets use `leanCompareConfig` (the
same `minTotalSeconds` floor) so each per-rung ratio compares steady-state
medians on both sides. This replaces the earlier fixed shape whose every
FLINT median pinned at the `~52 ms` driver-startup floor, leaving no
eligible rung.

Per-call overhead is now the steady-state persistent-driver round-trip
(stdin/stdout JSON request plus reply), measured per
`SPEC/benchmarking.md §"External comparators" §"Process call"` as the
warm-driver median on the smallest registered input, whose FLINT
algorithm work is sub-microsecond: `19.428 µs` for Rabin (rung `n = 8`)
and `33.879 µs` for DDF (rung `n = 12`). This is a per-call floor; the
JSON-marshalling component grows mildly with polynomial degree, so the
constant-overhead model slightly understates overhead at the top rungs.
Raw ratios are `FLINT median / Lean median` (lower means FLINT is
faster); on every rung where overhead exceeds 5% of the FLINT median the
overhead-adjusted ratio `(FLINT median − overhead) / Lean median` is also
recorded. A rung is eligible for the gating-goal verdict when overhead is
≤ 50% of the FLINT median and per-call wall time is within the
`≤ 1 s` soft / `≤ 10 s` hard ceiling.

Measurement commands at commit `3ad7817b` on `carica` (Apple M2 Ultra,
macOS 14.6.1), `HEX_FLINT_BENCH_PYTHON=python3`, python-flint `0.8.0`:

```sh
lake exe hexberlekamp_bench compare \
    Hex.BerlekampBench.runRabinTestChecksum{8,10,12,16,20,24,32,40,48,56,64} \
    Hex.BerlekampBench.runFlintRabinTestChecksum{8,10,12,16,20,24,32,40,48,56,64} \
    --export-file reports/bench-results/hex-berlekamp-rabin-compare.json
lake exe hexberlekamp_bench compare \
    Hex.BerlekampBench.runDistinctDegreeChecksum{12,16,20,24,32,40,48,64,80,96} \
    Hex.BerlekampBench.runFlintDistinctDegreeChecksum{12,16,20,24,32,40,48,64,80,96} \
    --export-file reports/bench-results/hex-berlekamp-ddf-compare.json
```

(the Lean and FLINT targets are interleaved rung-by-rung on the actual
command line). Export artefacts:
`reports/bench-results/hex-berlekamp-rabin-compare.json`, SHA-256
`9d85f268956099a4df99ded885dbeda2c25cb4a96e6f795a0b9bc4f922f41942`;
`reports/bench-results/hex-berlekamp-ddf-compare.json`, SHA-256
`225e85f1483a513701ffa5f0b01a85e01635b42a9db290c058fef37715f9cc57`.

### FLINT `nmod_poly.is_irreducible` vs Rabin

Per-call overhead `19.428 µs` (warm-driver round-trip, rung `n = 8`).

| n | Lean median | FLINT median | raw ratio | adjusted ratio | eligible |
|---:|---:|---:|---:|---:|:---:|
| 8 | 0.775 ms | 19.428 µs | 0.0251x | — | no |
| 10 | 1.587 ms | 23.246 µs | 0.0146x | 0.00240x | no |
| 12 | 2.276 ms | 25.082 µs | 0.0110x | 0.00248x | no |
| 16 | 5.623 ms | 34.988 µs | 0.00622x | 0.00277x | no |
| 20 | 11.036 ms | 37.278 µs | 0.00338x | 0.00162x | no |
| 24 | 16.621 ms | 47.494 µs | 0.00286x | 0.00169x | yes |
| 32 | 36.726 ms | 67.924 µs | 0.00185x | 0.00132x | yes |
| 40 | 79.722 ms | 75.643 µs | 0.000949x | 0.000705x | yes |
| 48 | 126.661 ms | 105.176 µs | 0.000830x | 0.000677x | yes |
| 56 | 222.325 ms | 151.275 µs | 0.000680x | 0.000593x | yes |
| 64 | 328.185 ms | 193.108 µs | 0.000588x | 0.000529x | yes |

Eligible range `n = 24 … 64` (six rungs): below `n = 24` the round-trip
overhead is more than half the FLINT median, and the `n = 8` row is the
overhead measurement itself. Across the eligible range the FLINT median
grows with degree while staying three to four orders of magnitude below
the Lean median, so the raw ratio falls monotonically from `0.00286x`
(`n = 24`) to `0.000588x` (`n = 64`) — a diverging trend with FLINT
pulling steadily further ahead. Overhead-adjustment moves the ratio in
the same direction (FLINT looks faster still), so it does not change the
verdict. Gating-goal verdict at the largest eligible rung (`n = 64`):
**fails** — Lean's `runRabinTestChecksum` is `~1700x` slower than FLINT's
`is_irreducible`, not at least as fast.

### FLINT `nmod_poly.factor_distinct_deg` vs DDF

Per-call overhead `33.879 µs` (warm-driver round-trip, rung `n = 12`).
The DDF fixed targets use an opaque timing token for the fixed compare:
the conformance oracle compares monic-normalised degree buckets, while
the raw Lean and FLINT representative checksums are not a stable shared
observable.

| n | Lean median | FLINT median | raw ratio | adjusted ratio | eligible |
|---:|---:|---:|---:|---:|:---:|
| 12 | 6.916 ms | 33.879 µs | 0.00490x | — | no |
| 16 | 13.141 ms | 44.882 µs | 0.00342x | 0.000837x | no |
| 20 | 21.250 ms | 57.017 µs | 0.00268x | 0.00109x | no |
| 24 | 45.354 ms | 88.100 µs | 0.00194x | 0.00120x | yes |
| 32 | 77.882 ms | 81.074 µs | 0.00104x | 0.000606x | yes |
| 40 | 123.663 ms | 105.013 µs | 0.000849x | 0.000575x | yes |
| 48 | 225.748 ms | 162.508 µs | 0.000720x | 0.000570x | yes |
| 64 | 516.348 ms | 390.753 µs | 0.000757x | 0.000691x | yes |
| 80 | 886.891 ms | 407.712 µs | 0.000460x | 0.000422x | yes |
| 96 | 1.473 s | 503.831 µs | 0.000342x | 0.000319x | yes* |

`*` the `n = 96` Lean median (`1.473 s`) sits above the `1 s` soft cap
but within the `10 s` hard ceiling; it is kept to extend the trend.
Eligible range `n = 24 … 96`: below `n = 24` the round-trip overhead is
more than half the FLINT median. As with Rabin, the FLINT median grows
with degree but stays three orders of magnitude below the Lean median;
the raw ratio falls from `0.00194x` (`n = 24`) to `0.000342x` (`n = 96`),
again a diverging trend in FLINT's favour. Gating-goal verdict at the
largest eligible rung (`n = 96`): **fails** — Lean's
`runDistinctDegreeChecksum` is `~2900x` slower than FLINT's
`factor_distinct_deg`. The verdict is the same at the largest rung under
the `1 s` soft cap (`n = 80`, `~2200x` slower).

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

- Both gating goals fail at the largest eligible rung. The comparator
  measurement shape is now valid — `warmupFirstIter` plus the raised
  `minTotalSeconds` floor amortise the persistent driver out of the
  per-call median, so the eligible range is `n = 24 … 64` for Rabin and
  `n = 24 … 96` for DDF rather than empty. But on those eligible rungs
  FLINT is three to four orders of magnitude faster than Lean
  (`runRabinTestChecksum` is `~1700x` slower than `is_irreducible` at
  `n = 64`; `runDistinctDegreeChecksum` is `~2900x` slower than
  `factor_distinct_deg` at `n = 96`). The SPEC goal is that Lean be at
  least as fast as FLINT at the largest eligible rung; it is not.
  HexBerlekamp should not re-claim Phase 4 until the Rabin and
  distinct-degree kernels close that gap — this is an algorithm/constant-
  factor gap in the executable Lean implementations, not a
  measurement-harness artefact.
- The raw FLINT ratio diverges (lower is faster for FLINT/Lean) across
  both eligible ranges: Rabin falls from `0.00286x` (`n = 24`) to
  `0.000588x` (`n = 64`), DDF from `0.00194x` (`n = 24`) to `0.000342x`
  (`n = 96`). FLINT pulls steadily further ahead as the degree grows, so
  the gap is widening, not a fixed offset.
