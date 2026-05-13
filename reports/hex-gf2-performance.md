# HexGF2 Performance Report

## Bench Targets

- `Hex.GF2Bench.runPureClmulChecksum`: `n`
- `Hex.GF2Bench.runClmulChecksum`: `n`
- `Hex.GF2Bench.runAddChecksum`: `n`
- `Hex.GF2Bench.runMulChecksum`: `n * n`
- `Hex.GF2Bench.runShiftLeftChecksum`: `n`
- `Hex.GF2Bench.runShiftRightChecksum`: `n`
- `Hex.GF2Bench.runDivChecksum`: `n * n`
- `Hex.GF2Bench.runModChecksum`: `n * n`
- `Hex.GF2Bench.runGcdChecksum`: `n * n`
- `Hex.GF2Bench.runXGcdChecksum`: `n * n`
- `Hex.GF2Bench.runGF2nAddChecksum`: `n`
- `Hex.GF2Bench.runGF2nMulChecksum`: `n`
- `Hex.GF2Bench.runGF2nInvChecksum`: `n`
- `Hex.GF2Bench.runGF2nDivChecksum`: `n`
- `Hex.GF2Bench.runGF2nPowChecksum`: `Nat.log2 (n + 1)`
- `Hex.GF2Bench.runGF2nPolyMulChecksum`: `n`
- `Hex.GF2Bench.runGF2nPolyInvChecksum`: `n`
- `Hex.GF2Bench.runGF2nPolyDivChecksum`: `n`
- `Hex.GF2Bench.runGF2nPolyPowChecksum`: `Nat.log2 (n + 1)`
- `Hex.GF2Bench.runPackedGcdCompareChecksum`: `packedGcdCompareComplexity n`
- `Hex.GF2Bench.runFp2GcdCompareChecksum`: `n * n`
- `Hex.GF2Bench.runPackedBerlekampCompareChecksum`: `packedBerlekampCompareComplexity n`
- `Hex.GF2Bench.runFp2BerlekampCompareChecksum`: `n * n`

Paired Hex/NTL informational comparator fixed registrations (per
`SPEC/Libraries/hex-gf2.md §"External comparators"` and
`SPEC/benchmarking.md §"External comparators" §"Process call"`):

- `runAdd{4096,8192,16384,32768,65536,131072,262144}` ↔
  `runNtlAdd{…}` (NTL `add`)
- `runMul{16,24,32,48,64,96,128,192,256,384,512,768,1024,1536,2048}` ↔
  `runNtlMul{…}` (NTL `mul`)
- `runDiv{16,24,32,48,64,96,128,192,256,384,512,768,1024}` ↔
  `runNtlDiv{…}` (NTL `div` quotient)
- `runMod{16,24,32,48,64,96,128,192,256,384,512,768,1024}` ↔
  `runNtlMod{…}` (NTL `rem` modular reduction)
- `runGcd{16,24,32,48,64,96,128,192,256,384,512,768,1024,1536}` ↔
  `runNtlGcd{…}` (NTL `gcd`)

All paired Hex/NTL targets share their fixture prep (`prepBinaryInput`,
`prepDivInput`, `prepGcdInput`) so `lean-bench`'s `hashes_agree` flag
joins on a real common domain. The five surfaces are the SPEC-named
packed-word GF(2)[x] operations.

## Verdicts

Scientific run at commit `85c88fcecc4955768ebcb787c4d14c59cdaed778` on
`carica` (Apple M2 Ultra, macOS 14.6.1), running every registered
hexgf2_bench target plus the 124 paired Hex/NTL fixed comparator rungs:

```sh
lake exe hexgf2_bench run $(lake exe hexgf2_bench list | awk '/^  Hex\./ {print $1}') \
    --export-file reports/bench-results/hex-gf2-85c88fc.json
```

The run used deterministic benchmark inputs from `HexGF2/Bench.lean` and
`HexGF2Bench.lean`; random seeds are not involved. The harness recorded
`85c88fc-dirty` because this worktree carries the pod-managed
`.claude/CLAUDE.md` change plus the in-flight HO-27 bench wiring.
Export artefact: `reports/bench-results/hex-gf2-85c88fc.json`, SHA-256
`f4f53ad82188bb6b57028ac20c8b2adcae47fd9294af599ce2e75cbb4fa01afd`.

- `Hex.GF2Bench.runPureClmulChecksum`: consistent with declared complexity
  (`β=+0.023`, parameters `1024..16384`, final hash `0x50e935653c8ec85b`).
- `Hex.GF2Bench.runClmulChecksum`: consistent with declared complexity
  (`β=-0.005`, parameters `65536..1048576`, final hash `0x1d791dabf32c7619`).
- `Hex.GF2Bench.runAddChecksum`: consistent with declared complexity
  (`β=+0.012`, parameters `4096..65536`, final hash `0x78c97f3bdcc10000`).
- `Hex.GF2Bench.runMulChecksum`: consistent with declared complexity
  (`β=-0.009`, parameters `16..128`, final hash `0x94ca57f890aeff7e`).
- `Hex.GF2Bench.runShiftLeftChecksum`: consistent with declared complexity
  (`β=-0.016`, parameters `4096..65536`, final hash `0xb69c55c31cce8000`).
- `Hex.GF2Bench.runShiftRightChecksum`: consistent with declared complexity
  (`β=-0.003`, parameters `4096..65536`, final hash `0x5edcf6ea5c7da445`).
- `Hex.GF2Bench.runDivChecksum`: consistent with declared complexity
  (`β=-0.014`, parameters `16..128`, final hash `0x5e31ad7a7929d63d`).
- `Hex.GF2Bench.runModChecksum`: consistent with declared complexity
  (`β=+0.013`, parameters `16..128`, final hash `0x1e654fc788e21384`).
- `Hex.GF2Bench.runGcdChecksum`: consistent with declared complexity
  (`β=-0.030`, parameters `16..128`, final hash `0xbf58476d1ce4e5bd`).
- `Hex.GF2Bench.runXGcdChecksum`: consistent with declared complexity
  (`β=-0.045`, parameters `16..128`, final hash `0x4485a0f767c61d69`).
- `Hex.GF2Bench.runGF2nAddChecksum`: consistent with declared complexity
  (`β=+0.005`, parameters `4096..65536`, final hash `0xb004958d67aef5de`).
- `Hex.GF2Bench.runGF2nMulChecksum`: consistent with declared complexity
  (`β=-0.010`, parameters `1024..16384`, final hash `0x6e7df9f15c10ff5e`).
- `Hex.GF2Bench.runGF2nInvChecksum`: consistent with declared complexity
  (`β=+0.001`, parameters `256..4096`, final hash `0xdf420f0867d2dbc0`).
- `Hex.GF2Bench.runGF2nDivChecksum`: consistent with declared complexity
  (`β=-0.011`, parameters `256..4096`, final hash `0xaa8761853c77b53b`).
- `Hex.GF2Bench.runGF2nPowChecksum`: consistent with declared complexity
  (`β=-0.025`, parameters `1048576..268435456`, final hash `0xe1`).
- `Hex.GF2Bench.runGF2nPolyMulChecksum`: consistent with declared complexity
  (`β=+0.009`, parameters `64..1024`, final hash `0x83e1705ae3cc5750`).
- `Hex.GF2Bench.runGF2nPolyInvChecksum`: consistent with declared complexity
  (`β=-0.011`, parameters `16..256`, final hash `0xd2b0a9094ecd3e22`).
- `Hex.GF2Bench.runGF2nPolyDivChecksum`: consistent with declared complexity
  (`β=-0.002`, parameters `16..256`, final hash `0xa2ca28b0008d11bc`).
- `Hex.GF2Bench.runGF2nPolyPowChecksum`: consistent with declared complexity
  (`β=+0.007`, parameters `1048576..268435456`, final hash
  `0xa60a5daa46f09188`).
- `Hex.GF2Bench.runPackedGcdCompareChecksum`: consistent with declared
  complexity (`β=-0.100`, parameters `8..64`, final hash
  `0xbf58476d1ce4e5ba`).
- `Hex.GF2Bench.runFp2GcdCompareChecksum`: consistent with declared
  complexity (`β=+0.004`, parameters `8..64`, final hash
  `0xbf58476d1ce4e5ba`).
- `Hex.GF2Bench.runPackedBerlekampCompareChecksum`: consistent with declared
  complexity (`β=-0.036`, parameters `8..64`, final hash
  `0xc1fd68f0bfde229`).
- `Hex.GF2Bench.runFp2BerlekampCompareChecksum`: consistent with declared
  complexity (`β=-0.018`, parameters `8..64`, final hash
  `0xc1fd68f0bfde229`).

The 62 paired Hex/NTL fixed-comparator registrations also passed: each
Hex target and its paired NTL call returned the same observed hash at
every rung (every `setup_fixed_benchmark` pair appears as a
`"hashes_agree": true` entry in the export). The agreement covers the
add, mul, div quotient, rem, and gcd surfaces across the full ladder,
confirming Hex's packed-word `GF2Poly` reduction and NTL's hand-tuned
`GF2X` agree on every measured input.

Smoke wiring was also checked with:

```sh
lake exe hexgf2_bench list
lake exe hexgf2_bench verify
```

`verify` passed all 147 registered benchmarks at the same commit
(23 parametric + 124 paired fixed comparator rungs).

## Comparator Ratios

`SPEC/Libraries/hex-gf2.md §"External comparators"` names
`NTL GF2X via persistent C++ subprocess driver` (matching
`libraries.yml: HexGF2.phase4.comparators[0].tool`) as the
`informational` external comparator for HexGF2, scoped to the five
packed-word GF(2)[x] operations the SPEC text names: `add`, `mul`,
`div` quotient, `rem` modular reduction, `gcd`. The comparator is wired
through the persistent C++ subprocess driver
(`scripts/oracle/gf2_ntl_bench_driver.cc`, built on-demand by
`scripts/oracle/setup_gf2_ntl_driver.sh`); `HexGF2/Bench.lean` reuses
the `Child.takeStdin` + `IO.Ref (Option NtlPersistentComparator)`
pattern HexLLL HO-16 uses for the Isabelle comparator, with one driver
spawned per `lake exe hexgf2_bench run` invocation and one
fresh-spawned driver per measured `setup_fixed_benchmark` repeat.

Pairings:

- `runNtlAdd*` ↔ `runAdd*` (NTL `add` against `GF2Poly.add`)
- `runNtlMul*` ↔ `runMul*` (NTL `mul` against `GF2Poly.mul`)
- `runNtlDiv*` ↔ `runDiv*` (NTL `DivRem` quotient against `GF2Poly.div`)
- `runNtlMod*` ↔ `runMod*` (NTL `rem` against `GF2Poly.mod`)
- `runNtlGcd*` ↔ `runGcd*` (NTL `GCD` against `GF2Poly.gcd`)

`runXGcdChecksum`, `runShiftLeftChecksum`, `runShiftRightChecksum`,
`runClmulChecksum` / `runPureClmulChecksum`, and the `runGF2n*` /
`runGF2nPoly*` extension-field targets are out of scope of the
SPEC-named comparator coverage and declare absence with the
`structural-layer` reason per the same SPEC subsection.

### Per-call overhead

NTL driver per-call overhead is measured by spawning the driver and
sending one `ping` request (returns the constant `0` checksum after
parsing the request line). Eleven trials on the audit host: median
**24.247 ms**, min 23.398 ms, max 75.474 ms (the max is the cold-cache
first spawn; subsequent spawns settle in the `23.4 – 26.6 ms` band).
The post-startup steady-state per-request overhead is **~0.8 µs** as
measured by piping 10000 `ping` requests through a single driver
process (5 trials, median 32.6 ms total ⇒ ~7.6 µs per request including
startup, so ~0.8 µs steady-state). The `setup_fixed_benchmark` shape
spawns one bench child per measured repeat, so every NTL median below
includes one ~24 ms driver startup. The `adjusted ratio` column
subtracts the 24.2 ms overhead from the NTL median when positive, then
divides by the Hex median. A rung is **eligible** under
`SPEC/benchmarking.md §"Headline reports" §"Comparator ratios"` when
both (a) the 24.2 ms overhead is at most 50% of measured NTL wall time
on that rung (i.e. wall ≥ 48.4 ms) and (b) per-call wall time is at
most the 10 s hard ceiling.

The `add` surface is a special case: NTL `GF2X` addition is a 64-bit
`memcpy + XOR` whose algorithmic cost is sub-millisecond at every
fixture size in the eligible parametric range, so for `add` the NTL
wall time at large rungs is dominated by **hex-input marshaling** (the
driver protocol passes each `GF2Poly` as a hex-encoded byte string).
The `add` rows are reported for completeness; the ratio there is
between Hex's `GF2Poly.add` and NTL's `(parse hex) + add + (mix
words)` round-trip, not against NTL's raw kernel. The mul/div/rem/gcd
surfaces are bounded by NTL's algorithmic cost across the upper rungs
and are the load-bearing comparator surfaces.

### NTL `GF2X` `add` vs `runAddChecksum`

Input family `packed-bitwise-core`, declared complexity `n`. Hex's
packed XOR against NTL's `GF2X` addition. NTL wall time is dominated
by marshaling at every reported rung, so the eligibility flag is
present but the ratios are informational rather than algorithmic.

| n | Hex median | NTL median | raw ratio | adjusted ratio | eligible |
|---:|---:|---:|---:|---:|:---:|
| 4096 | 548.937 µs | 48.661 ms | 88.646x | 44.561x | yes |
| 8192 | 1.160 ms | 89.048 ms | 76.793x | 55.923x | yes |
| 16384 | 2.278 ms | 81.154 ms | 35.628x | 25.004x | yes |
| 32768 | 4.613 ms | 100.803 ms | 21.853x | 16.607x | yes |
| 65536 | 9.255 ms | 152.564 ms | 16.484x | 13.869x | yes |
| 131072 | 18.929 ms | 278.244 ms | 14.699x | 13.421x | yes |
| 262144 | 37.390 ms | 462.044 ms | 12.357x | 11.710x | yes |

Trend: adjusted ratio converges from `44.6x` at `n = 4096` toward
`~12x` at `n = 262144` — Hex `GF2Poly.add` scales linearly in `n`,
NTL's round-trip cost scales linearly in `n` because the
hex-marshaling buffer grows linearly, so the ratio decays as the
fixed-cost portion of the marshaling protocol amortises. The
asymptote sits at the marshaling-throughput ratio of the protocol
itself, not at the underlying `add` kernel ratio; this surface is
not a useful audit signal for the `GF2Poly.add` implementation.

### NTL `GF2X` `mul` vs `runMulChecksum`

Input family `packed-euclidean`, declared complexity `n²`. Hex's
schoolbook packed-word multiplication (with Karatsuba crossover named
in the algorithm table) against NTL's Karatsuba/FFT-tuned `GF2X` mul.

| n | Hex median | NTL median | raw ratio | adjusted ratio | eligible |
|---:|---:|---:|---:|---:|:---:|
| 16 | 42.580 µs | 49.178 ms | 1154.947x | 586.605x | yes |
| 24 | 98.250 µs | 49.199 ms | 500.750x | 254.439x | yes |
| 32 | 169.520 µs | 52.920 ms | 312.175x | 169.419x | yes |
| 48 | 383.677 µs | 45.843 ms | 119.483x | 56.409x | no |
| 64 | 663.270 µs | 56.851 ms | 85.713x | 49.227x | yes |
| 96 | 1.458 ms | 45.963 ms | 31.518x | 14.924x | no |
| 128 | 2.660 ms | 56.404 ms | 21.203x | 12.106x | yes |
| 192 | 5.707 ms | 56.384 ms | 9.880x | 5.640x | yes |
| 256 | 10.660 ms | 51.073 ms | 4.791x | 2.521x | yes |
| 384 | 23.088 ms | 48.354 ms | 2.094x | 1.046x | no |
| 512 | 41.078 ms | 43.688 ms | 1.064x | 0.474x | no |
| 768 | 91.809 ms | 46.917 ms | 0.511x | 0.247x | no |
| 1024 | 163.822 ms | 59.660 ms | 0.364x | 0.216x | yes |
| 1536 | 369.000 ms | 58.325 ms | 0.158x | 0.092x | yes |
| 2048 | 663.958 ms | 51.014 ms | 0.077x | 0.040x | yes |

Trend: raw ratio falls monotonically across the entire ladder from
`1155x` at `n = 16` (Hex is fast, NTL is dominated by the ~25 ms
startup floor) through unity at `n = 512` to `0.077x` at `n = 2048`
(NTL is ~13x faster than Hex on wall time). Within the eligible rungs
the adjusted ratio decays from `2.5x` at `n = 256` (Hex still ahead
after subtracting startup) to `0.040x` at `n = 2048` (NTL spends ~4%
of Hex's wall time on the same packed-word multiplication); NTL's
asymptotic advantage is the Karatsuba/FFT crossover Hex's declared
algorithm table does not exercise. Eligibility flips on and off in
the mid-range because NTL's algorithmic work at intermediate `n` is
right at the 24 ms overhead floor; the trend across the whole ladder
is unambiguous despite the flicker.

### NTL `GF2X` `div` vs `runDivChecksum`

Input family `packed-euclidean`, declared complexity `n²`. Hex's
schoolbook long-division quotient against NTL's `DivRem` quotient.

| n | Hex median | NTL median | raw ratio | adjusted ratio | eligible |
|---:|---:|---:|---:|---:|:---:|
| 16 | 1.457 ms | 52.434 ms | 35.979x | 19.373x | yes |
| 24 | 3.079 ms | 47.927 ms | 15.564x | 7.705x | no |
| 32 | 5.341 ms | 46.015 ms | 8.616x | 4.085x | no |
| 48 | 12.817 ms | 44.439 ms | 3.467x | 1.579x | no |
| 64 | 22.156 ms | 58.975 ms | 2.662x | 1.570x | yes |
| 96 | 49.152 ms | 55.987 ms | 1.139x | 0.647x | yes |
| 128 | 84.926 ms | 53.182 ms | 0.626x | 0.341x | yes |
| 192 | 189.075 ms | 54.157 ms | 0.286x | 0.158x | yes |
| 256 | 346.675 ms | 49.657 ms | 0.143x | 0.073x | yes |
| 384 | 786.856 ms | 47.118 ms | 0.060x | 0.029x | no |
| 512 | 1.379 s | 74.954 ms | 0.054x | 0.037x | yes |
| 768 | 3.263 s | 65.984 ms | 0.020x | 0.013x | yes |
| 1024 | 6.094 s | 55.951 ms | 0.009x | 0.005x | yes |

Trend: NTL crosses Hex around `n = 96` and runs ~110x faster than
Hex at the top eligible rung (`n = 1024`, adjusted ratio `0.005x`).
NTL's faster long-division-style inner loop and the same Karatsuba/FFT
crossover that helps `mul` dominate Hex's schoolbook divModAux at
this regime.

### NTL `GF2X` `rem` vs `runModChecksum`

Input family `packed-euclidean`, declared complexity `n²`. Hex's
long-division remainder against NTL's `rem`.

| n | Hex median | NTL median | raw ratio | adjusted ratio | eligible |
|---:|---:|---:|---:|---:|:---:|
| 16 | 1.430 ms | 101.676 ms | 71.125x | 54.196x | yes |
| 24 | 2.930 ms | 78.165 ms | 26.680x | 18.420x | yes |
| 32 | 5.221 ms | 46.145 ms | 8.838x | 4.203x | no |
| 48 | 12.808 ms | 52.985 ms | 4.137x | 2.247x | yes |
| 64 | 21.870 ms | 62.706 ms | 2.867x | 1.761x | yes |
| 96 | 48.692 ms | 60.164 ms | 1.236x | 0.739x | yes |
| 128 | 83.643 ms | 69.950 ms | 0.836x | 0.547x | yes |
| 192 | 190.078 ms | 63.461 ms | 0.334x | 0.207x | yes |
| 256 | 336.862 ms | 46.923 ms | 0.139x | 0.067x | no |
| 384 | 772.176 ms | 45.613 ms | 0.059x | 0.028x | no |
| 512 | 1.391 s | 58.222 ms | 0.042x | 0.024x | yes |
| 768 | 3.235 s | 61.285 ms | 0.019x | 0.011x | yes |
| 1024 | 5.990 s | 64.377 ms | 0.011x | 0.007x | yes |

Trend: NTL crosses Hex around `n = 128` and runs ~140x faster than
Hex at the top eligible rung (`n = 1024`, adjusted ratio `0.007x`).
The shape mirrors `div`'s trend; NTL's `rem` shares the same fast
DivRem path internally, while Hex's `mod` reuses the same `divModAux`
schoolbook helper as `div`.

### NTL `GF2X` `gcd` vs `runGcdChecksum`

Input family `packed-euclidean`, declared complexity `n²`. Hex's
Euclidean gcd (`xgcdAux`-driven) against NTL's `GCD`.

| n | Hex median | NTL median | raw ratio | adjusted ratio | eligible |
|---:|---:|---:|---:|---:|:---:|
| 16 | 2.749 ms | 45.145 ms | 16.424x | 7.620x | no |
| 24 | 6.101 ms | 45.271 ms | 7.421x | 3.454x | no |
| 32 | 10.395 ms | 52.601 ms | 5.060x | 2.732x | yes |
| 48 | 23.311 ms | 49.539 ms | 2.125x | 1.087x | yes |
| 64 | 40.480 ms | 46.713 ms | 1.154x | 0.556x | no |
| 96 | 90.936 ms | 47.722 ms | 0.525x | 0.259x | no |
| 128 | 162.311 ms | 44.503 ms | 0.274x | 0.125x | no |
| 192 | 338.129 ms | 46.134 ms | 0.136x | 0.065x | no |
| 256 | 619.762 ms | 58.074 ms | 0.094x | 0.055x | yes |
| 384 | 1.391 s | 55.636 ms | 0.040x | 0.023x | yes |
| 512 | 2.464 s | 48.641 ms | 0.020x | 0.010x | yes |
| 768 | 5.486 s | 48.841 ms | 0.009x | 0.004x | yes |
| 1024 | 9.984 s | 67.320 ms | 0.007x | 0.004x | yes |
| 1536 | 22.459 s | 54.035 ms | 0.002x | 0.001x | yes |

Trend: NTL crosses Hex around `n = 64` and runs ~1000x faster than
Hex at the top eligible rung (`n = 1536`, adjusted ratio `0.001x`).
NTL's `GCD` uses subquadratic GCD variants (half-gcd) that Hex's
Euclidean reduction does not; the gap accelerates more sharply with
`n` than `div` / `rem` because Hex's gcd inner loop iterates the
linear-time long-division cost across `O(n)` reduction steps.

### Within-Lean packed-vs-generic comparison (retained from prior report)

Beyond the NTL informational comparator, the `hexgf2_bench` executable
root registers a cross-library `GF2Poly` versus `FpPoly 2` comparison
under the `packed-vs-generic-comparison` input family. Median per-call
wallclocks at the top of each comparison ladder (`n = 64`, this run):

- `runPackedGcdCompareChecksum`: 14.10 ms; `runFp2GcdCompareChecksum`:
  1.412 s — packed is ~100x faster than the generic `FpPoly 2` path on
  shared GF(2) coefficient inputs.
- `runPackedBerlekampCompareChecksum`: 9.77 ms;
  `runFp2BerlekampCompareChecksum`: 418.72 ms — packed is ~43x faster
  on the Berlekamp-style Frobenius-column construction.

Both ratios sit comfortably inside the "substantially faster than the
generic `FpPoly 2` path (up to 64x for addition-heavy workloads)"
claim in `SPEC/Libraries/hex-gf2.md`. The GCD ratio's overshoot of the
SPEC's "up to 64x" headline reflects that the packed long-division
inner loop is dominated by 64-bit XOR/shift word ops, while the
generic `FpPoly 2` path pays per-bit `ZMod64`-wrapped arithmetic.

## Profile

Profiles were recorded with `samply record --save-only --unstable-presymbolicate`
at the same commit on `carica` (Apple M2 Ultra, macOS 14.6.1), at the default
1 kHz sampling rate. The raw Firefox Profiler JSON artefacts and their
`.syms.json` symbol sidecars are developer-local and are not committed. Each
profile sums samples from the `hexgf2_bench` worker child processes only, not
the orchestrator (whose wallclock is dominated by `__read_nocancel` waits for
the child stdout that LeanBench's subprocess-isolated harness produces). All
percentages below are leaf counts and inclusive counts as a fraction of those
child-only samples.

### `packed-word-clmul`

Command:

```sh
samply record --save-only --unstable-presymbolicate -o reports/bench-results/profiles/hex-gf2-clmul-6404c87bac75.json -- lake exe hexgf2_bench run Hex.GF2Bench.runClmulChecksum
```

Representative case: deterministic UInt64 sample pairs for the extern
carry-less word multiplication, parameters `65536..1048576`, no seed. Leaf
samples were kernel/syscall wait 65.6%, Lean runtime 19.8%, allocation/free
9.4%, own HexGF2 code 3.4%, other 1.8%, GMP 0.1%. Inclusive HexGF2 cost was
led by the `runClmulChecksum` bench loop closure (27.6%) and the `Array.range`
fold over samples (27.4%), with the extern `lean_hex_clmul_u64` wrapper
itself contributing 23.6% inclusive. Subordinate `lean_box_uint64` (14.9%) and
`lean_alloc_ctor` (11.7%) inclusive cost is the boxing of the `(hi, lo)`
`UInt64 × UInt64` extern result on each call. The dominant work maps to the
registered carry-less word multiplication target.

### `packed-bitwise-core`

Command:

```sh
samply record --save-only --unstable-presymbolicate -o reports/bench-results/profiles/hex-gf2-bitwise-6404c87bac75.json -- lake exe hexgf2_bench run Hex.GF2Bench.runAddChecksum
```

Representative case: deterministic same-size packed GF(2) polynomials for XOR
addition, parameters `4096..65536`, no seed. Leaf samples were kernel/syscall
wait 65.5%, Lean runtime 10.2%, allocation/free 9.5%, own HexGF2 code 9.2%,
other 5.6%. Inclusive HexGF2 cost was led by `runAddChecksum` and the bench
loop (26.1%), `GF2Poly.add` (13.5%), and `GF2Poly.trimTrailingZeroWordsList`
(8.2%). The `lean_list_to_array` runtime tail (7.9%) reflects the trim path's
list-to-array round-trip on the addition result. The dominant work maps to the
registered packed addition target.

### `packed-euclidean`

Command:

```sh
samply record --save-only --unstable-presymbolicate -o reports/bench-results/profiles/hex-gf2-euclidean-6404c87bac75.json -- lake exe hexgf2_bench run Hex.GF2Bench.runGcdChecksum
```

Representative case: deterministic same-size packed GF(2) polynomials for
Euclidean gcd, parameters `16..128`, no seed. Leaf samples were
kernel/syscall wait 65.5%, Lean runtime 14.9%, allocation/free 10.5%, own
HexGF2 code 4.8%, other 4.3%, GMP 0.1%. Inclusive HexGF2 cost was led by
`runGcdChecksum`, `GF2Poly.gcd`, and `GF2Poly.xgcdAux` (each 30.7%); the
inner schoolbook multiplication path appeared via `GF2Poly.mul` (16.2%),
`GF2Poly.mulWords` (16.2%), the foldl over packed words (16.1%), and
`xorClmulAt` (14.7%). The dominant work maps to the registered packed
Euclidean target and to its underlying packed multiplication helper.

### `gf2n-aes-field`

Command:

```sh
samply record --save-only --unstable-presymbolicate -o reports/bench-results/profiles/hex-gf2-aes-field-6404c87bac75.json -- lake exe hexgf2_bench run Hex.GF2Bench.runGF2nMulChecksum
```

Representative case: deterministic AES-modulus single-word extension-field
multiplication chains, parameters `1024..16384`, no seed. Leaf samples were
kernel/syscall wait 66.1%, allocation/free 10.3%, own HexGF2 code 9.2%, Lean
runtime 8.8%, other 5.2%, GMP 0.3%. Inclusive HexGF2 cost was led by
`GF2Poly.packedReduceWord` (28.0%), `GF2Poly.mod` (26.0%), and
`GF2Poly.divModAux` (25.2%); the registered bench loop and its closures
contributed 18.4%, with `GF2n.mul` itself at 17.6% and `GF2n.reduce` at 12.3%.
The dominant work maps to the registered AES-modulus single-word
multiplication target via the `GF2Poly.mod`/`packedReduceWord` reduction
helper called from `GF2n.mul`.

### `gf2n-poly-quotient`

Command:

```sh
samply record --save-only --unstable-presymbolicate -o reports/bench-results/profiles/hex-gf2-poly-quotient-6404c87bac75.json -- lake exe hexgf2_bench run Hex.GF2Bench.runGF2nPolyMulChecksum
```

Representative case: deterministic degree-128 packed quotient-field
multiplication chains, parameters `64..1024`, no seed. Leaf samples were
kernel/syscall wait 65.6%, allocation/free 11.7%, Lean runtime 8.9%, other
7.1%, own HexGF2 code 6.7%, GMP 0.1%. Inclusive HexGF2 cost was led by
`runGF2nPolyMulChecksum` (29.6%), `GF2nPoly.reducePoly`, `GF2Poly.mod`, and
`GF2Poly.divModAux` (each 28.3%), with subordinate `GF2Poly.add` (10.1%) and
`GF2Poly.shiftLeft` (7.5%). The dominant work maps to the registered packed
quotient-field multiplication target via the `reducePoly`/`mod` reduction
helper.

### `packed-vs-generic-comparison`

Command:

```sh
samply record --save-only --unstable-presymbolicate -o reports/bench-results/profiles/hex-gf2-compare-6404c87bac75.json -- lake exe hexgf2_bench run Hex.GF2Bench.runPackedGcdCompareChecksum
```

Representative case: shared deterministic GF(2) coefficient fixtures for
packed `GF2Poly` versus generic `FpPoly 2` polynomial gcd, parameters
`8..64`, no seed. Leaf samples were kernel/syscall wait 75.2%,
allocation/free 6.8%, Lean runtime 6.2%, other 6.0%, own HexGF2 code 3.3%,
GMP 2.5%. Inclusive HexGF2 cost was led by the shared-domain prep path —
`prepCompareInput`, `fp2DenseQuotientPair`, and `DensePoly.mul` (each 19.7%
inclusive) — followed by the packed-side gcd at 12.2% inclusive
(`runPackedGcdCompareChecksum`, `GF2Poly.gcd`, `GF2Poly.xgcdAux` each
12.2%). `lean_hex_zmod64_mul` (15.5%) is the generic-side `FpPoly 2`
multiplication used inside `fp2DenseQuotientPair`; LeanBench hoists `prep`
out of the timed verdict loop, so this prep cost is not double-counted in
the bench verdict above. The shared-prep design is intentional —
`prepCompareInput` constructs both packed and generic operands from the same
deterministic coefficient fixture so `compare` joins on a real common
domain — and the dominant timed work maps to the registered packed-gcd
target.

## Concerns

- NTL `GF2X` `mul` / `div` / `rem` / `gcd` show a diverging trend
  against Hex `GF2Poly` across the eligible upper rungs of each
  ladder. At `n = 2048` (mul) and `n = 1024–1536` (div / rem / gcd)
  NTL spends `0.04x – 0.001x` of Hex's wall time on the same surface
  after subtracting the 24 ms driver-startup overhead; the gap
  accelerates with `n`. NTL's Karatsuba/FFT-tuned inner loops and
  subquadratic GCD beat Hex's schoolbook packed-word reduction by
  roughly two to three orders of magnitude in the upper eligible
  range. This is the structural gap `SPEC/Libraries/hex-gf2.md
  §"External comparators"`'s `informational` rationale named in
  advance ("NTL ships hand-tuned word-level inner loops for
  GF(2)[x]; Hex's `GF2Poly` is the verified packed-word algorithmic
  surface"). The comparator is `informational`, so the divergence
  does not produce a gating-goal verdict, but is recorded here per
  `SPEC/benchmarking.md §"Headline reports" §"Comparator ratios"`
  ("a diverging trend … is itself an audit-found Concern even when
  the highest-rung verdict happens to pass").
- The NTL `add` surface measurements are dominated by the
  hex-marshaling round-trip cost across the bench-driver protocol;
  NTL `GF2X` addition is sub-millisecond at every reported rung but
  the wall time includes parsing the hex-encoded operand bytes
  (linear in `n`). The reported `add` rows are kept for completeness;
  they are not an audit signal for `GF2Poly.add`'s implementation.
  A follow-up HO could rewire the driver to accept raw binary frames
  instead of hex if the `add` comparator becomes load-bearing later.
