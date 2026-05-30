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

Profiles were recorded with `scripts/profile/run_profile.sh` at commit
`eec3a76fab8c` on `carica` (Apple M2 Ultra, macOS 14.6.1), sampling at
`samply 0.13.1`'s 999 Hz interval. The bench binary used lean-bench
`91412dba8350` (`LeanBench.TimedRegions`; the JSON row reports library version
`0.1.0`). The raw Firefox Profiler JSON artefacts, sidecars, and retained raw
inputs are developer-local and are not committed. Each profile below is filtered
to samples from the bench thread inside LeanBench timed regions only; input
preparation, autotuning between probes, result hashing, process startup, and
process exit are excluded by the sidecar windows. All percentages are leaf
counts or inclusive counts as a fraction of the retained bench-thread samples.

### `dense-reduction`

Command:

```sh
scripts/profile/run_profile.sh \
    ./.lake/build/bin/hexgfqring_bench \
    Hex.GFqRingBench.runReduceModChecksum 256 5000000000
```

Representative case: deterministic dense `F_65537`-coefficient polynomial of
size `2 * (n + 1) + 1 = 515` reduced through `Hex.GFqRing.reduceMod` against
the deterministic dense modulus of degree `n + 1 = 257`, parameter `n = 256`,
no seed. Child row: `inner_repeats=256`,
`per_call_nanos=17236222.656250`, `result_hash=0xf371d3c6f9329331`. Filtered
profile: `/tmp/hex-profile-runReduceModChecksum-256.json.gz`.

Diagnostics quoted from the filtering postprocessor:

```text
bench_thread_tid=4351417
regions_total=2
total_timed_ms=4429.627667
expected_samples_bench_thread=4425.2
retained_samples_bench_thread=4422
rejected_samples_bench_thread=10
off_bench_thread_samples_in_window=0
samply_interval_ms=1.001001
spawn_anchor_wall_ns=1780141144435093000
spawn_anchor_mono_ns=329178333913041
sidecar_mono_anchor_ns=329178930047750
```

Leaf samples were allocation/free 51.9%, GMP big-integer arithmetic 16.4%,
Lean runtime 15.1%, other system/Lean/library frames 11.0%, and own
HexGfqRing/HexPolyFp code 5.6%. The large allocation/free share is inside the
timed remainder loop: `mi_free`, `mi_malloc_small`, and macOS
`libsystem_malloc` leaves are reached through the same coefficient update stack
as the arithmetic leaves, not through input construction. Inclusive own-code
cost was led by `Hex.GFqRingBench.runReduceModChecksum` (100.0%) ->
`Hex.GFqRing.reduceMod` (100.0%) -> `Hex.DensePoly.divModArray` (100.0%) ->
`Hex.DensePoly.divModArrayAux` (99.8%) ->
`Hex.DensePoly.subtractScaledShiftStep` (91.5%). Per-coefficient work appears
as `Hex.ZMod64.mul` (43.3%), `Hex.ZMod64.sub` (42.8%), and
`Hex.ZMod64.complementWord` (38.1%). The dominant work maps to the registered
`runReduceModChecksum` target via the
`reduceMod -> divModArray -> subtractScaledShiftStep` remainder-by-shift chain,
exactly as the `n^2` cost model predicts.

### `quotient-arithmetic`

Command:

```sh
scripts/profile/run_profile.sh \
    ./.lake/build/bin/hexgfqring_bench \
    Hex.GFqRingBench.runMulChecksum 256 5000000000
```

Representative case: deterministic dense `F_65537` canonical-rep quotient
pairs of size `n + 1 = 257` multiplied modulo the deterministic dense modulus,
parameter `n = 256`, no seed. Child row: `inner_repeats=128`,
`per_call_nanos=29683093.421875`, `result_hash=0xeb5bd94c74ddcdcd`. Filtered
profile: `/tmp/hex-profile-runMulChecksum-256.json.gz`.

Diagnostics quoted from the filtering postprocessor:

```text
bench_thread_tid=4352045
regions_total=2
total_timed_ms=3826.603125
expected_samples_bench_thread=3822.8
retained_samples_bench_thread=3809
rejected_samples_bench_thread=9
off_bench_thread_samples_in_window=2
samply_interval_ms=1.001001
spawn_anchor_wall_ns=1780141154646502000
spawn_anchor_mono_ns=329188545410625
sidecar_mono_anchor_ns=329188881497041
```

Leaf samples were allocation/free 50.6%, Lean runtime 16.6%, GMP big-integer
arithmetic 13.8%, other system/Lean/library frames 12.5%, and own
HexGfqRing/HexPolyFp code 6.5%. Inclusive own-code cost split between
`Hex.GFqRing.mul -> Hex.DensePoly.mul` (37.3% / 37.3%) for the schoolbook
product and `Hex.GFqRing.reduceMod -> Hex.DensePoly.divModArray ->
Hex.DensePoly.divModArrayAux` (62.7% / 62.7% / 62.7%) for the post-product
remainder; the heavier share is the reduction half because the dividend has
degree `2(n + 1)` after multiplication. Per-coefficient work appears as
`Hex.ZMod64.mul` (52.7%), `Hex.ZMod64.sub` (28.9%), and
`Hex.ZMod64.complementWord` (25.7%) inside `subtractScaledShiftStep` (58.2%).
The dominant work maps to the registered `runMulChecksum` target via
`GFqRing.mul` (the schoolbook `DensePoly.mul`) followed by the same
`GFqRing.reduceMod` remainder chain measured in `dense-reduction`, matching
the `n^2` cost model: the multiplication and the reduction are both `O(n^2)`
in the modulus degree, so combined throughput is also `O(n^2)`.

The dominant inclusive costs in both profiles all map to registered
`HexGfqRing/Bench.lean` targets. The newly visible dominant allocation leaves
are attributable to the registered dense-reduction and quotient-multiplication
timed regions rather than to unmeasured preparation or hashing. No unattributed
dominant cost was observed.

## Concerns
