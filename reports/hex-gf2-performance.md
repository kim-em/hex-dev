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

## Verdicts

Scientific run at commit `6404c87bac7598f50e059af0f843c1f4d8c8a5a6` on `carica`
(Apple M2 Ultra, macOS 14.6.1), command:

```sh
lake exe hexgf2_bench run Hex.GF2Bench.runPureClmulChecksum Hex.GF2Bench.runClmulChecksum Hex.GF2Bench.runAddChecksum Hex.GF2Bench.runMulChecksum Hex.GF2Bench.runShiftLeftChecksum Hex.GF2Bench.runShiftRightChecksum Hex.GF2Bench.runDivChecksum Hex.GF2Bench.runModChecksum Hex.GF2Bench.runGcdChecksum Hex.GF2Bench.runXGcdChecksum Hex.GF2Bench.runGF2nAddChecksum Hex.GF2Bench.runGF2nMulChecksum Hex.GF2Bench.runGF2nInvChecksum Hex.GF2Bench.runGF2nDivChecksum Hex.GF2Bench.runGF2nPowChecksum Hex.GF2Bench.runGF2nPolyMulChecksum Hex.GF2Bench.runGF2nPolyInvChecksum Hex.GF2Bench.runGF2nPolyDivChecksum Hex.GF2Bench.runGF2nPolyPowChecksum Hex.GF2Bench.runPackedGcdCompareChecksum Hex.GF2Bench.runFp2GcdCompareChecksum Hex.GF2Bench.runPackedBerlekampCompareChecksum Hex.GF2Bench.runFp2BerlekampCompareChecksum --export-file reports/bench-results/hex-gf2-6404c87bac75.json
```

The run used deterministic benchmark inputs from `HexGF2/Bench.lean` and
`HexGF2Bench.lean`; random seeds are not involved. The harness recorded
`6404c87-dirty` because this worktree had an unrelated pre-existing
`.claude/CLAUDE.md` modification. Export artefact:
`reports/bench-results/hex-gf2-6404c87bac75.json`, SHA-256
`10f21af41007cca052eaf94a1eb14b7c054c30898665fc6edef056c2fba46bda`.

- `Hex.GF2Bench.runPureClmulChecksum`: consistent with declared complexity
  (`β=-0.014`, parameters `1024..16384`, final hash `0x50e935653c8ec85b`).
- `Hex.GF2Bench.runClmulChecksum`: consistent with declared complexity
  (`β=-0.006`, parameters `65536..1048576`, final hash `0x1d791dabf32c7619`).
- `Hex.GF2Bench.runAddChecksum`: consistent with declared complexity
  (`β=-0.025`, parameters `4096..65536`, final hash `0x78c97f3bdcc10000`).
- `Hex.GF2Bench.runMulChecksum`: consistent with declared complexity
  (`β=-0.016`, parameters `16..128`, final hash `0x94ca57f890aeff7e`).
- `Hex.GF2Bench.runShiftLeftChecksum`: consistent with declared complexity
  (`β=-0.037`, parameters `4096..65536`, final hash `0xb69c55c31cce8000`).
- `Hex.GF2Bench.runShiftRightChecksum`: consistent with declared complexity
  (`β=+0.011`, parameters `4096..65536`, final hash `0x5edcf6ea5c7da445`).
- `Hex.GF2Bench.runDivChecksum`: consistent with declared complexity
  (`β=-0.043`, parameters `16..128`, final hash `0x5e31ad7a7929d63d`).
- `Hex.GF2Bench.runModChecksum`: consistent with declared complexity
  (`β=+0.001`, parameters `16..128`, final hash `0x1e654fc788e21384`).
- `Hex.GF2Bench.runGcdChecksum`: consistent with declared complexity
  (`β=-0.032`, parameters `16..128`, final hash `0xbf58476d1ce4e5bd`).
- `Hex.GF2Bench.runXGcdChecksum`: consistent with declared complexity
  (`β=-0.036`, parameters `16..128`, final hash `0x4485a0f767c61d69`).
- `Hex.GF2Bench.runGF2nAddChecksum`: consistent with declared complexity
  (`β=+0.002`, parameters `4096..65536`, final hash `0xb004958d67aef5de`).
- `Hex.GF2Bench.runGF2nMulChecksum`: consistent with declared complexity
  (`β=-0.002`, parameters `1024..16384`, final hash `0x6e7df9f15c10ff5e`).
- `Hex.GF2Bench.runGF2nInvChecksum`: consistent with declared complexity
  (`β=-0.022`, parameters `256..4096`, final hash `0xdf420f0867d2dbc0`).
- `Hex.GF2Bench.runGF2nDivChecksum`: consistent with declared complexity
  (`β=-0.008`, parameters `256..4096`, final hash `0xaa8761853c77b53b`).
- `Hex.GF2Bench.runGF2nPowChecksum`: consistent with declared complexity
  (`β=-0.020`, parameters `1048576..268435456`, final hash `0xe1`).
- `Hex.GF2Bench.runGF2nPolyMulChecksum`: consistent with declared complexity
  (`β=+0.039`, parameters `64..1024`, final hash `0x83e1705ae3cc5750`).
- `Hex.GF2Bench.runGF2nPolyInvChecksum`: consistent with declared complexity
  (`β=-0.011`, parameters `16..256`, final hash `0xd2b0a9094ecd3e22`).
- `Hex.GF2Bench.runGF2nPolyDivChecksum`: consistent with declared complexity
  (`β=+0.021`, parameters `16..256`, final hash `0xa2ca28b0008d11bc`).
- `Hex.GF2Bench.runGF2nPolyPowChecksum`: consistent with declared complexity
  (`β=+0.003`, parameters `1048576..268435456`, final hash
  `0xa60a5daa46f09188`).
- `Hex.GF2Bench.runPackedGcdCompareChecksum`: consistent with declared
  complexity (`β=-0.098`, parameters `8..64`, final hash
  `0xbf58476d1ce4e5ba`).
- `Hex.GF2Bench.runFp2GcdCompareChecksum`: consistent with declared
  complexity (`β=+0.013`, parameters `8..64`, final hash
  `0xbf58476d1ce4e5ba`).
- `Hex.GF2Bench.runPackedBerlekampCompareChecksum`: consistent with declared
  complexity (`β=+0.013`, parameters `8..64`, final hash
  `0xc1fd68f0bfde229`).
- `Hex.GF2Bench.runFp2BerlekampCompareChecksum`: consistent with declared
  complexity (`β=-0.002`, parameters `8..64`, final hash
  `0xc1fd68f0bfde229`).

Smoke wiring was also checked with:

```sh
lake exe hexgf2_bench list
lake exe hexgf2_bench verify
```

`verify` passed all 23 registered benchmarks at the same commit.

## Comparator Ratios

`SPEC/Libraries/hex-gf2.md` does not name an external Phase-4 comparator for
`HexGF2`, so there are no `phase4.comparators` ratios to record. The SPEC does
require the `GF2Poly`-versus-`FpPoly 2` cross-library comparison registered at
the `hexgf2_bench` executable root; those four targets share deterministic
input fixtures and are reported under the `packed-vs-generic-comparison`
input family. Median per-call wallclocks at the top of each comparison ladder
(`n = 64`, scientific run above) are:

- `runPackedGcdCompareChecksum`: 13.05 ms; `runFp2GcdCompareChecksum`: 1335.24
  ms — packed is ≈102x faster than the generic `FpPoly 2` path on shared
  GF(2) coefficient inputs.
- `runPackedBerlekampCompareChecksum`: 9.79 ms;
  `runFp2BerlekampCompareChecksum`: 407.51 ms — packed is ≈41x faster on the
  Berlekamp-style Frobenius-column construction at the same parameter.

Both ratios sit comfortably inside the "substantially faster than the generic
`FpPoly 2` path (up to 64x for addition-heavy workloads)" claim in
`SPEC/Libraries/hex-gf2.md`. The GCD ratio's overshoot of the SPEC's "up to
64x" headline reflects that the packed long-division inner loop is dominated
by 64-bit XOR/shift word ops, while the generic `FpPoly 2` path pays per-bit
`ZMod64`-wrapped arithmetic.

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
