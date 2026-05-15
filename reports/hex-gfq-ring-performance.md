# HexGfqRing Performance Report

## Bench Targets

- `Hex.GFqRingBench.runReduceModChecksum`: `n * n`
- `Hex.GFqRingBench.runOfPolyReprChecksum`: `n * n`
- `Hex.GFqRingBench.runAddChecksum`: `n`
- `Hex.GFqRingBench.runMulChecksum`: `n * n`
- `Hex.GFqRingBench.runNegSubChecksum`: `n`
- `Hex.GFqRingBench.runPowChecksum`: `n * n * Nat.log2 (n + 1)`
- `Hex.GFqRingBench.runNsmulNatCastChecksum`: `n * Nat.log2 (n + 1)`

## Verdicts

Scientific run at commit `58fc57b3775d` on `carica` (Apple M2 Ultra,
macOS 14.6.1), command:

```sh
lake exe hexgfqring_bench run \
    Hex.GFqRingBench.runReduceModChecksum \
    Hex.GFqRingBench.runOfPolyReprChecksum \
    Hex.GFqRingBench.runAddChecksum \
    Hex.GFqRingBench.runMulChecksum \
    Hex.GFqRingBench.runNegSubChecksum \
    Hex.GFqRingBench.runPowChecksum \
    Hex.GFqRingBench.runNsmulNatCastChecksum \
    --export-file reports/bench-results/hex-gfq-ring-58fc57b3775d.json
```

The run used the deterministic dense `F_65537` benchmark inputs constructed in
`HexGfqRing/Bench.lean`; no random seeds are involved. The harness recorded
`58fc57b-dirty` because this worktree carried an unrelated pre-existing
`.claude/CLAUDE.md` modification. Export artefact:
`reports/bench-results/hex-gfq-ring-58fc57b3775d.json`, SHA-256
`8a520657a5831d3a85123381fb30af5a590ab072b9e2b371fe1eb32b85e3d2ee`.

- `Hex.GFqRingBench.runReduceModChecksum`: consistent with declared
  complexity (`cMin=257.387, cMax=277.951, β=-0.048`, parameters `32..256`,
  final hash `0xf371d3c6f9329331`).
- `Hex.GFqRingBench.runOfPolyReprChecksum`: consistent with declared
  complexity (`cMin=253.382, cMax=285.501, β=-0.070`, parameters `32..256`,
  final hash `0x23d2ab1b563934bd`).
- `Hex.GFqRingBench.runAddChecksum`: consistent with declared complexity
  (`cMin=62.700, cMax=63.152, β=-0.000`, parameters `1024..16384`, final
  hash `0x85d136a41d4b8326`).
- `Hex.GFqRingBench.runMulChecksum`: consistent with declared complexity
  (`cMin=402.550, cMax=429.240, β=-0.038`, parameters `32..256`, final hash
  `0xeb5bd94c74ddcdcd`).
- `Hex.GFqRingBench.runNegSubChecksum`: consistent with declared complexity
  (`cMin=405.544, cMax=409.187, β=+0.001`, parameters `1024..16384`, final
  hash `0xabd96493530c0e96`).
- `Hex.GFqRingBench.runPowChecksum`: consistent with declared complexity
  (`cMin=857.257, cMax=934.635, β=-0.050`, parameters `32..256`, final hash
  `0x183fffe2c35e8615`).
- `Hex.GFqRingBench.runNsmulNatCastChecksum`: consistent with declared
  complexity (`cMin=73.558, cMax=76.661, β=-0.016`, parameters
  `1024..16384`, final hash `0x4b573cec38265a21`).

Smoke wiring was also checked at the same commit with:

```sh
lake exe hexgfqring_bench list
lake exe hexgfqring_bench verify
```

`verify` passed all seven registered benchmarks.

## Comparator Ratios

`SPEC/Libraries/hex-gfq-ring.md` declares that no external Phase-4 performance
comparator is required for `HexGfqRing`. The reason is `structural-layer`:
`HexGfqRing` implements the general quotient ring `F_p[x]/(f)` for any
nonconstant modulus, including reducible moduli, while FLINT `fq_default`
constructs finite fields and rejects reducible moduli. The finite-field subset
is covered by `HexGfqField`'s `fq_default` comparator, where irreducibility is
part of the library contract. Consequently there are no `phase4.comparators`
ratios to record for `HexGfqRing`, and there is no internal `compare` group
declared across the seven registrations.

## Profile

Profiles were recorded with `samply record --save-only
--unstable-presymbolicate` at commit `58fc57b3775d` on `carica` (Apple M2
Ultra, macOS 14.6.1) at the default 1 kHz sampling rate. The raw Firefox
Profiler JSON artefacts and their `.syms.json` symbol sidecars are
developer-local and are not committed; symbol attribution was done by mapping
each frame's RVA against the bench binary's samply-emitted symbol table. Each
profile sums samples from the main worker thread in the `hexgfqring_bench`
child (the LeanBench-spawned `_child` process running the registered
function), not the orchestrator or its lock-wait support threads. All
percentages below are leaf counts and inclusive counts as a fraction of those
worker-thread samples.

### `dense-reduction`

Command:

```sh
lake exe hexgfqring_bench profile Hex.GFqRingBench.runReduceModChecksum \
    --param 256 --target-inner-nanos 5000000000 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        -o /tmp/hex-profiles/hex-gfq-ring-reduce-mod-58fc57b3775d.json --"
```

Representative case: deterministic dense `F_65537`-coefficient polynomial of
size `2 * (n + 1) + 1 = 515` reduced through `Hex.GFqRing.reduceMod` against
the deterministic dense modulus of degree `n + 1 = 257`, parameter `n = 256`,
no seed. Child row: `inner_repeats=256`,
`per_call_nanos=16999750.816406`, `result_hash=0xf371d3c6f9329331`. The
worker thread recorded `4395` total sample weight; sidecar:
`/tmp/hex-profiles/hex-gfq-ring-reduce-mod-58fc57b3775d.syms.json`.

Leaf samples were other system frames 57.5%, GMP big-integer arithmetic
17.2%, Lean runtime 15.6%, own HexGfqRing/HexPolyFp code 5.3%, and
allocation/free 4.3%. Inclusive own-code cost was led by
`Hex.GFqRingBench.runReduceModChecksum` (99.4%) ->
`Hex.GFqRing.reduceMod` (99.4%) -> `Hex.DensePoly.divModArray` (99.3%) ->
`Hex.DensePoly.divModArrayAux` (99.2%) ->
`Hex.DensePoly.subtractScaledShiftStep` (90.8%). Per-coefficient work appears
as `Hex.ZMod64.mul` (43.3%), `Hex.ZMod64.sub` (42.1%), and
`Hex.ZMod64.complementWord` (37.2%). The dominant work maps to the registered
`runReduceModChecksum` target via the
`reduceMod -> divModArray -> subtractScaledShiftStep` remainder-by-shift chain,
exactly as the `n^2` cost model predicts.

### `quotient-arithmetic`

Command:

```sh
lake exe hexgfqring_bench profile Hex.GFqRingBench.runMulChecksum \
    --param 256 --target-inner-nanos 5000000000 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        -o /tmp/hex-profiles/hex-gfq-ring-mul-58fc57b3775d.json --"
```

Representative case: deterministic dense `F_65537` canonical-rep quotient
pairs of size `n + 1 = 257` multiplied modulo the deterministic dense modulus,
parameter `n = 256`, no seed. Child row: `inner_repeats=128`,
`per_call_nanos=27692107.421875`, `result_hash=0xeb5bd94c74ddcdcd`. The
worker thread recorded `3603` total sample weight; sidecar:
`/tmp/hex-profiles/hex-gfq-ring-mul-58fc57b3775d.syms.json`.

Leaf samples were other system frames 55.5%, Lean runtime 17.1%, GMP
big-integer arithmetic 15.5%, own HexGfqRing/HexPolyFp code 6.6%, and
allocation/free 5.4%. Inclusive own-code cost split between
`Hex.GFqRing.mul -> Hex.DensePoly.mul` (37.4%) for the schoolbook product and
`Hex.GFqRing.reduceMod -> Hex.DensePoly.divModArray ->
Hex.DensePoly.divModArrayAux` (61.7% / 61.7% / 61.6%) for the post-product
remainder; the heavier share is the reduction half because the dividend has
degree `2(n + 1)` after multiplication. Per-coefficient work appears as
`Hex.ZMod64.mul` (53.9%), `Hex.ZMod64.sub` (26.4%), and
`Hex.ZMod64.complementWord` (23.8%) inside `subtractScaledShiftStep` (56.6%).
The dominant work maps to the registered `runMulChecksum` target via
`GFqRing.mul` (the schoolbook `DensePoly.mul`) followed by the same
`GFqRing.reduceMod` remainder chain measured in `dense-reduction`, matching
the `n^2` cost model: the multiplication and the reduction are both `O(n^2)`
in the modulus degree, so combined throughput is also `O(n^2)`.

The dominant inclusive costs in both profiles all map to registered
`HexGfqRing/Bench.lean` targets. No unattributed dominant cost was observed.

## Concerns
