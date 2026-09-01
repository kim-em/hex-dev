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
`HexGF2/SPEC/hex-gf2.md §"External comparators"` and
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

The parametric verdicts below come from the scientific run at commit
`85c88fcecc4955768ebcb787c4d14c59cdaed778` on `carica` (Apple M2 Ultra,
macOS 14.6.1). That run included the then-current fixed registrations, but its
fixed timings are superseded by the warmed `e44c4be1e` export in Comparator
Ratios and are not reused here:

```sh
lake exe hexgf2_bench run $(lake exe hexgf2_bench list | awk '/^  Hex\./ {print $1}') \
    --export-file reports/bench-results/hex-gf2-85c88fc.json
```

The run used deterministic benchmark inputs from `bench/HexGF2/Bench.lean`
and `bench/HexGF2Bench.lean`; random seeds are not involved. The harness recorded
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

The repaired `e44c4be1e` comparator export described below contains all 124
fixed registrations. Every registration has stable repeat hashes, and all 62
Hex/NTL pairs agree on their observed hash across addition, multiplication,
division quotient, remainder, and GCD.

Smoke wiring was also checked with:

```sh
lake exe hexgf2_bench list
lake exe hexgf2_bench verify
```

`verify` passed all 147 registered benchmarks after the protocol repair
(23 parametric + 124 paired fixed comparator rungs).

## Comparator Ratios

`HexGF2/SPEC/hex-gf2.md`, §"External comparators", names
NTL GF2X via persistent C++ subprocess driver as an informational performance
comparator for multiplication, division,
remainder, and GCD. Addition is retained only as a same-input
correctness/protocol anchor because hex serialization dominates its linear
kernel.

The paired fixed registrations were rerun after the protocol and contract
repair at commit `e44c4be1e80e26a244aeb40a5d01e046ad687ab5` on
`chungus2` (AMD EPYC 9455, Linux x86_64), pinned to CPU 6:

```sh
HEX_GF2_NTL_DRIVER=.cache/oracles/gf2-ntl/gf2_ntl_bench_driver
lake exe hexgf2_bench list | awk '/\[fixed\]/{print $1}' |
  xargs taskset -c 6 lake exe hexgf2_bench run \
    --export-file reports/bench-results/hex-gf2-e44c4be-issue9804-warmed.json
```

The export contains all 124 fixed registrations and 560 successful outer
repeats. Every registration has internally stable hashes, and all 62 Hex/NTL
pairs agree on their observed hash. The harness records `e44c4be-dirty` only
because the freshly generated, untracked HexPoly export already existed when
this run began; the source commit is the full `e44c4be1e...` recorded in the
artifact. Its SHA-256 is
`8c4cb4ab9177356317535fa96493d404e2f252c438c1c9b01fe1c8dbf1433689`.

### Protocol overhead and eligibility

Every NTL registration sets `warmupFirstIter := true`. The discarded first
call starts the driver, and the timed inner-repeat batch reuses it. The paired
Hex registration uses the same `minTotalSeconds := 0.2` timing floor.

Fresh one-request driver processes took 3 ms median over 11 trials. That
one-time startup is excluded by the warmup. A 100000-request `ping` run took
0.024 s median over five trials, an upper bound of 0.24 µs per steady-state
round trip including shell-pipeline cost and amortized startup. The smallest
NTL operation median below is 13.073 µs, so protocol overhead is at most 1.9%;
no adjusted ratio is required by `SPEC/benchmarking.md`'s 5% rule.

For performance tables, a row is eligible exactly when both observed medians
are at most ten seconds and the protocol floor passes. The ratio is `NTL /
Hex`; values below one mean NTL is faster.

### Addition correctness/protocol anchor

| n | Hex median | NTL median | NTL / Hex | hashes agree |
|---:|---:|---:|---:|:---:|
| 4096 | 291.226 µs | 2.130 ms | 7.3128x | yes |
| 8192 | 581.914 µs | 4.347 ms | 7.4696x | yes |
| 16384 | 1.222 ms | 8.802 ms | 7.2047x | yes |
| 32768 | 2.450 ms | 26.580 ms | 10.8469x | yes |
| 65536 | 5.667 ms | 37.476 ms | 6.6129x | yes |
| 131072 | 9.888 ms | 76.238 ms | 7.7105x | yes |
| 262144 | 21.539 ms | 153.512 ms | 7.1270x | yes |

All seven pairs agree on the result hash. The NTL round trip stays in a
roughly 6.6–10.9x band because parsing and emitting the hex-framed operands
dominates `GF2X` addition. These rows establish protocol throughput and
correctness only; they are not NTL addition-kernel performance evidence and
carry no performance verdict.

### Multiplication performance

| n | Hex median | NTL median | NTL / Hex | eligible |
|---:|---:|---:|---:|:---:|
| 16 | 14.757 µs | 13.073 µs | 0.8859x | yes |
| 24 | 32.006 µs | 16.470 µs | 0.5146x | yes |
| 32 | 57.524 µs | 20.830 µs | 0.3621x | yes |
| 48 | 133.918 µs | 31.433 µs | 0.2347x | yes |
| 64 | 222.701 µs | 41.170 µs | 0.1849x | yes |
| 96 | 500.180 µs | 66.399 µs | 0.1328x | yes |
| 128 | 870.983 µs | 89.242 µs | 0.1025x | yes |
| 192 | 1.985 ms | 154.131 µs | 0.0777x | yes |
| 256 | 3.538 ms | 201.789 µs | 0.0570x | yes |
| 384 | 8.251 ms | 363.565 µs | 0.0441x | yes |
| 512 | 15.395 ms | 471.484 µs | 0.0306x | yes |
| 768 | 38.200 ms | 916.804 µs | 0.0240x | yes |
| 1024 | 74.750 ms | 1.188 ms | 0.0159x | yes |
| 1536 | 293.789 ms | 2.429 ms | 0.0083x | yes |
| 2048 | 607.435 ms | 3.076 ms | 0.0051x | yes |

The ratio falls smoothly from 0.886x to 0.0051x across fifteen eligible
rungs. That divergence is expected by the normative contract: NTL dispatches
to Karatsuba/FFT kernels while Hex currently uses packed schoolbook
multiplication. It is an informational optimization signal, not a Concern.

### Division performance

| n | Hex median | NTL median | NTL / Hex | eligible |
|---:|---:|---:|---:|:---:|
| 16 | 948.173 µs | 20.573 µs | 0.0217x | yes |
| 24 | 1.910 ms | 29.913 µs | 0.0157x | yes |
| 32 | 3.170 ms | 39.690 µs | 0.0125x | yes |
| 48 | 7.176 ms | 62.870 µs | 0.0088x | yes |
| 64 | 12.107 ms | 85.316 µs | 0.0070x | yes |
| 96 | 26.348 ms | 143.913 µs | 0.0055x | yes |
| 128 | 45.595 ms | 195.661 µs | 0.0043x | yes |
| 192 | 101.838 ms | 366.406 µs | 0.0036x | yes |
| 256 | 183.389 ms | 487.403 µs | 0.0027x | yes |
| 384 | 432.351 ms | 943.821 µs | 0.0022x | yes |
| 512 | 765.782 ms | 1.218 ms | 0.0016x | yes |
| 768 | 1.834 s | 2.521 ms | 0.0014x | yes |
| 1024 | 3.355 s | 3.301 ms | 0.0010x | yes |

The ratio falls at every rung, from 0.0217x to 0.0010x over thirteen
eligible points. This is the expected fast-division versus long-division
difference declared in the SPEC.

### Remainder performance

| n | Hex median | NTL median | NTL / Hex | eligible |
|---:|---:|---:|---:|:---:|
| 16 | 954.122 µs | 20.489 µs | 0.0215x | yes |
| 24 | 1.908 ms | 29.941 µs | 0.0157x | yes |
| 32 | 3.147 ms | 39.944 µs | 0.0127x | yes |
| 48 | 7.175 ms | 62.573 µs | 0.0087x | yes |
| 64 | 12.185 ms | 86.021 µs | 0.0071x | yes |
| 96 | 25.902 ms | 144.624 µs | 0.0056x | yes |
| 128 | 46.491 ms | 196.975 µs | 0.0042x | yes |
| 192 | 101.618 ms | 401.089 µs | 0.0039x | yes |
| 256 | 185.976 ms | 487.782 µs | 0.0026x | yes |
| 384 | 413.494 ms | 942.284 µs | 0.0023x | yes |
| 512 | 777.010 ms | 1.220 ms | 0.0016x | yes |
| 768 | 2.180 s | 2.539 ms | 0.0012x | yes |
| 1024 | 3.326 s | 3.287 ms | 0.0010x | yes |

The thirteen-rung curve mirrors division and falls from 0.0215x to 0.0010x.
NTL's fast remainder path and Hex's long remainder loop are explicitly
different algorithm classes in the normative contract.

### GCD performance

| n | Hex median | NTL median | NTL / Hex | eligible |
|---:|---:|---:|---:|:---:|
| 16 | 3.136 ms | 16.123 µs | 0.0051x | yes |
| 24 | 7.029 ms | 23.881 µs | 0.0034x | yes |
| 32 | 13.463 ms | 34.599 µs | 0.0026x | yes |
| 48 | 26.341 ms | 58.878 µs | 0.0022x | yes |
| 64 | 46.656 ms | 92.917 µs | 0.0020x | yes |
| 96 | 100.191 ms | 185.893 µs | 0.0019x | yes |
| 128 | 181.476 ms | 301.839 µs | 0.0017x | yes |
| 192 | 390.045 ms | 594.575 µs | 0.0015x | yes |
| 256 | 741.485 ms | 962.572 µs | 0.0013x | yes |
| 384 | 1.545 s | 2.981 ms | 0.0019x | yes |
| 512 | 2.775 s | 4.364 ms | 0.0016x | yes |
| 768 | 6.181 s | 9.386 ms | 0.0015x | yes |
| 1024 | 11.057 s | 12.910 ms | 0.0012x | no |
| 1536 | 26.511 s | 26.713 ms | 0.0010x | no |

The eligible curve contains twelve rungs and ends at `n = 768`. It falls
from 0.0051x into an upper-ladder 0.0013–0.0019x band, consistent with NTL
half-GCD against Hex's Euclidean GCD. The `n = 1024` and `n = 1536` Hex
medians exceed the ten-second hard ceiling and are explicitly ineligible;
they are retained only to show where the measured ladder crosses the limit.

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
