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
- `runGcd{16,24,32,48,64,96,128,192,256,384,512,768}` ↔
  `runNtlGcd{…}` (NTL `gcd`)

All paired Hex/NTL targets share their fixture prep (`prepBinaryInput`,
`prepDivInput`, `prepGcdInput`) so `lean-bench`'s `hashes_agree` flag
joins on a real common domain. The five surfaces are the SPEC-named
packed-word GF(2)[x] operations.

## Verdicts

The parametric verdicts below come from the scientific run at commit
`85c88fcecc4955768ebcb787c4d14c59cdaed778` on `carica` (Apple M2 Ultra,
macOS 14.6.1). That run included the then-current fixed registrations, but its
fixed timings are superseded by the warmed `f4f013c63` export in Comparator
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

The repaired `f4f013c63` comparator export described below contains all 121
fixed registrations. Every registration has stable repeat hashes, and all 60
Hex/NTL pairs agree on their observed hash across addition, multiplication,
division quotient, remainder, and GCD.

Smoke wiring was also checked with:

```sh
lake exe hexgf2_bench list
lake exe hexgf2_bench verify
```

`verify` passed all 144 registered benchmarks after the protocol repair
(23 parametric + 120 paired fixed comparator rungs + one protocol-overhead
case).

## Comparator Ratios

`HexGF2/SPEC/hex-gf2.md`, §"External comparators", names
NTL GF2X via persistent C++ subprocess driver as an informational performance
comparator for multiplication, division,
remainder, and GCD. Addition is retained only as a same-input
correctness/protocol anchor because hex serialization dominates its linear
kernel.

The paired fixed registrations were rerun after the protocol and contract
repair at clean commit `f4f013c638460c621728e108c9b77988df8d2836` on
`chungus2` (AMD EPYC 9455, Linux x86_64), pinned to CPU 4:

```sh
HEX_GF2_NTL_DRIVER=.cache/oracles/gf2-ntl/gf2_ntl_bench_driver
lake exe hexgf2_bench list | awk '/\[fixed\]/{print $1}' |
  xargs taskset -c 4 lake exe hexgf2_bench run \
    --export-file reports/bench-results/hex-gf2-f4f013c-issue9804-warmed.json
```

The export contains all 121 fixed registrations and 553 successful outer
repeats. Every registration has internally stable hashes, and all 60 Hex/NTL
pairs agree on their observed hash. The harness records a clean source tree at
the full commit above. Its SHA-256 is
`a5d3b8504871ca1a614fb0ad53e851dea50bca85b81422272e205d384f3c1011`.

### Protocol overhead and eligibility

Both registrations in every Hex/NTL pair set `warmupFirstIter := true` and the
same `minTotalSeconds := 0.2` timing floor, and fixture preparation is outside
the timed closure. The discarded NTL call starts the driver, and the timed
inner-repeat batch reuses it. Startup is therefore represented only by the
discarded warmup and is not folded into the per-call overhead.

The registered synchronous `runNtlOverhead` case measures the steady-state
trivial `ping` round trip through the same persistent driver at 2.682 µs. An
adjusted ratio is shown wherever this exceeds 5% of the NTL operation median.
The floor is below 50% of every retained comparator median.

For performance tables, a row is eligible exactly when both observed medians
are at most ten seconds and the protocol floor passes. Rungs observed beyond
the hard ceiling are removed rather than measured as diagnostics. The ratio is
`NTL / Hex`; values below one mean the complete NTL process-call surface took
less time.

### Addition correctness/protocol anchor

| n | Hex median | NTL median | NTL / Hex | hashes agree |
|---:|---:|---:|---:|:---:|
| 4096 | 291.811 µs | 2.117 ms | 7.255x | yes |
| 8192 | 590.751 µs | 4.314 ms | 7.302x | yes |
| 16384 | 1.208 ms | 8.682 ms | 7.188x | yes |
| 32768 | 2.384 ms | 18.098 ms | 7.592x | yes |
| 65536 | 4.768 ms | 38.194 ms | 8.011x | yes |
| 131072 | 18.263 ms | 75.392 ms | 4.128x | yes |
| 262144 | 30.771 ms | 150.912 ms | 4.904x | yes |

All seven pairs agree on the result hash. The NTL round trip stays in a
roughly 4.1–8.0x band because parsing and emitting the hex-framed operands
dominates `GF2X` addition. These rows establish protocol throughput and
correctness only; they are not NTL addition-kernel performance evidence and
carry no performance verdict.

### Multiplication performance

| n | Hex median | NTL median | NTL / Hex | adjusted | eligible |
|---:|---:|---:|---:|---:|:---:|
| 16 | 14.832 µs | 11.748 µs | 0.792x | 0.611x | yes |
| 24 | 32.149 µs | 25.004 µs | 0.778x | 0.694x | yes |
| 32 | 57.294 µs | 22.074 µs | 0.385x | 0.338x | yes |
| 48 | 129.477 µs | 31.830 µs | 0.246x | 0.225x | yes |
| 64 | 224.837 µs | 67.923 µs | 0.302x | — | yes |
| 96 | 485.892 µs | 66.622 µs | 0.137x | — | yes |
| 128 | 880.677 µs | 88.332 µs | 0.100x | — | yes |
| 192 | 1.953 ms | 153.806 µs | 0.079x | — | yes |
| 256 | 3.572 ms | 199.979 µs | 0.056x | — | yes |
| 384 | 8.091 ms | 367.843 µs | 0.045x | — | yes |
| 512 | 15.697 ms | 474.405 µs | 0.030x | — | yes |
| 768 | 38.123 ms | 914.449 µs | 0.024x | — | yes |
| 1024 | 73.379 ms | 1.184 ms | 0.016x | — | yes |
| 1536 | 277.084 ms | 2.391 ms | 0.009x | — | yes |
| 2048 | 620.656 ms | 3.071 ms | 0.005x | — | yes |

The ratio falls overall from 0.792x to 0.005x. The measured NTL 11.6 build
links gf2x 1.3; NTL's source selects tuned base, Karatsuba, and gf2x-backed
multiplication paths while Hex currently uses packed schoolbook
multiplication. This operation-specific divergence is informational, not a
Concern.

### Division performance

| n | Hex median | NTL median | NTL / Hex | adjusted | eligible |
|---:|---:|---:|---:|---:|:---:|
| 16 | 932.723 µs | 20.285 µs | 0.022x | 0.019x | yes |
| 24 | 1.888 ms | 29.633 µs | 0.016x | 0.014x | yes |
| 32 | 3.627 ms | 39.361 µs | 0.011x | 0.010x | yes |
| 48 | 7.191 ms | 62.345 µs | 0.009x | — | yes |
| 64 | 11.959 ms | 84.255 µs | 0.007x | — | yes |
| 96 | 26.070 ms | 143.135 µs | 0.005x | — | yes |
| 128 | 45.683 ms | 196.143 µs | 0.004x | — | yes |
| 192 | 101.480 ms | 362.967 µs | 0.004x | — | yes |
| 256 | 182.168 ms | 487.402 µs | 0.003x | — | yes |
| 384 | 417.869 ms | 939.673 µs | 0.002x | — | yes |
| 512 | 771.461 ms | 1.214 ms | 0.002x | — | yes |
| 768 | 1.887 s | 2.523 ms | 0.001x | — | yes |
| 1024 | 3.363 s | 3.279 ms | 0.001x | — | yes |

The ratio falls overall from 0.022x to 0.001x over thirteen eligible points.
NTL switches to crossover division while Hex uses long division, matching the
operation-specific contract.

### Remainder performance

| n | Hex median | NTL median | NTL / Hex | adjusted | eligible |
|---:|---:|---:|---:|---:|:---:|
| 16 | 932.052 µs | 20.407 µs | 0.022x | 0.019x | yes |
| 24 | 1.942 ms | 30.076 µs | 0.015x | 0.014x | yes |
| 32 | 3.128 ms | 39.368 µs | 0.013x | 0.012x | yes |
| 48 | 7.091 ms | 62.234 µs | 0.009x | — | yes |
| 64 | 12.076 ms | 85.218 µs | 0.007x | — | yes |
| 96 | 26.107 ms | 144.280 µs | 0.006x | — | yes |
| 128 | 46.103 ms | 194.384 µs | 0.004x | — | yes |
| 192 | 105.627 ms | 365.591 µs | 0.003x | — | yes |
| 256 | 183.964 ms | 486.094 µs | 0.003x | — | yes |
| 384 | 416.334 ms | 938.305 µs | 0.002x | — | yes |
| 512 | 777.181 ms | 1.211 ms | 0.002x | — | yes |
| 768 | 1.848 s | 2.515 ms | 0.001x | — | yes |
| 1024 | 3.372 s | 3.261 ms | 0.001x | — | yes |

The thirteen-rung curve mirrors division and falls from 0.022x to 0.001x.
NTL's crossover remainder path and Hex's long remainder loop are explicitly
different algorithm classes in the normative contract.

### GCD performance

| n | Hex median | NTL median | NTL / Hex | adjusted | eligible |
|---:|---:|---:|---:|---:|:---:|
| 16 | 3.134 ms | 16.135 µs | 0.005x | 0.004x | yes |
| 24 | 6.908 ms | 24.197 µs | 0.004x | 0.003x | yes |
| 32 | 12.138 ms | 33.790 µs | 0.003x | 0.003x | yes |
| 48 | 26.221 ms | 58.719 µs | 0.002x | — | yes |
| 64 | 45.269 ms | 92.251 µs | 0.002x | — | yes |
| 96 | 100.367 ms | 185.122 µs | 0.002x | — | yes |
| 128 | 178.247 ms | 300.504 µs | 0.002x | — | yes |
| 192 | 386.469 ms | 591.403 µs | 0.002x | — | yes |
| 256 | 685.349 ms | 953.571 µs | 0.001x | — | yes |
| 384 | 1.551 s | 2.981 ms | 0.002x | — | yes |
| 512 | 2.780 s | 4.346 ms | 0.002x | — | yes |
| 768 | 6.244 s | 9.309 ms | 0.001x | — | yes |

The twelve-rung curve ends at `n = 768`, below the hard ceiling, and falls
from 0.005x into an upper-ladder 0.001–0.002x band. NTL 11.6 switches from its
Euclidean base to `HalfGCD` above its crossover, while Hex retains Euclidean
GCD. The former over-ceiling `n = 1024` and `n = 1536` registrations were
removed rather than timed contrary to the benchmark contract.

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
