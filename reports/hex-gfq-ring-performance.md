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

Scientific run at commit `28f9f6c95543` on `carica` (Apple M2 Ultra,
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
    --export-file reports/bench-results/hex-gfq-ring-28f9f6c95543.json
```

The run used the deterministic dense `F_65537` benchmark inputs
constructed in `HexGfqRing/Bench.lean`; no random seeds are involved.
The harness recorded `28f9f6c-dirty` because this worktree carried an
unrelated pre-existing `.claude/CLAUDE.md` modification and untracked
`.claude/` content. Export artefact:
`reports/bench-results/hex-gfq-ring-28f9f6c95543.json`, SHA-256
`7528bb9253e0c2a7e8a47df6b631bdc0bd978507f4ade1cea5cda9b882c82bf9`.

- `Hex.GFqRingBench.runReduceModChecksum`: consistent with declared
  complexity (`cMin=236.353, cMax=262.769, β=−0.064`,
  parameters `32..256`, final hash `0xf371d3c6f9329331`).
- `Hex.GFqRingBench.runOfPolyReprChecksum`: consistent with declared
  complexity (`cMin=237.192, cMax=267.150, β=−0.062`,
  parameters `32..256`, final hash `0x23d2ab1b563934bd`).
- `Hex.GFqRingBench.runAddChecksum`: consistent with declared
  complexity (`cMin=58.947, cMax=60.365, β=+0.006`,
  parameters `1024..16384`, final hash `0x85d136a41d4b8326`).
- `Hex.GFqRingBench.runMulChecksum`: consistent with declared
  complexity (`cMin=380.873, cMax=409.006, β=−0.029`,
  parameters `32..256`, final hash `0xeb5bd94c74ddcdcd`).
- `Hex.GFqRingBench.runNegSubChecksum`: consistent with declared
  complexity (`cMin=383.763, cMax=399.531, β=−0.009`,
  parameters `1024..16384`, final hash `0xabd96493530c0e96`).
- `Hex.GFqRingBench.runPowChecksum`: consistent with declared
  complexity (`cMin=832.233, cMax=925.970, β=−0.044`,
  parameters `32..256`, final hash `0x183fffe2c35e8615`).
- `Hex.GFqRingBench.runNsmulNatCastChecksum`: consistent with declared
  complexity (`cMin=71.416, cMax=77.698, β=−0.039`,
  parameters `1024..16384`, final hash `0x4b573cec38265a21`).

Smoke wiring was also checked at the same commit with:

```sh
lake exe hexgfqring_bench list
lake exe hexgfqring_bench verify
```

`verify` passed all seven registered benchmarks.

## Comparator Ratios

`SPEC/Libraries/hex-gfq-ring.md` does not name an external Phase-4
performance comparator for `HexGfqRing`, so there are no
`phase4.comparators` ratios to record. The library is the
underlying quotient-ring layer that downstream `HexGfqField`
benchmarks share, and there is no internal `compare` group declared
across the seven registrations.

## Profile

Profiles were recorded with
`samply record --save-only --unstable-presymbolicate` at commit
`28f9f6c95543` on `carica` (Apple M2 Ultra, macOS 14.6.1) at the
default 1 kHz sampling rate. The raw Firefox Profiler JSON
artefacts and their `.syms.json` symbol sidecars are
developer-local and are not committed; symbol attribution was done
by mapping each frame's RVA against the bench binary's
samply-emitted symbol table. Each profile sums samples from the
`hexgfqring_bench` worker child (the LeanBench-spawned `_child`
process running the registered function), not the orchestrator,
whose wallclock is dominated by `__read_nocancel` waits for the
child stdout. All percentages below are leaf counts and inclusive
counts as a fraction of those child-only samples.

### `dense-reduction`

Command:

```sh
lake exe hexgfqring_bench profile Hex.GFqRingBench.runReduceModChecksum \
    --param 256 --target-inner-nanos 5000000000 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        -o /tmp/hex-profiles/hex-gfq-ring-reduce-mod-28f9f6c95543.json --"
```

Representative case: deterministic dense `F_65537`-coefficient
polynomial of size `2 · (n + 1) + 1 = 515` reduced through
`Hex.GFqRing.reduceMod` against the deterministic dense modulus of
degree `n + 1 = 257`, parameter `n = 256`, no seed. Child row:
`inner_repeats=256`, `per_call_nanos=16491754.882812`,
`result_hash=0xf371d3c6f9329331`. Total `4245` non-empty samples.
Leaf samples were allocation/free 53.4%, GMP 17.5%, Lean runtime
15.4%, own HexGfqRing/HexPolyFp code 4.6%, other 9.1%. The
allocation/GMP weight reflects the `ZMod64`-on-`Nat`-of-`mpz`
arithmetic in the inner reduction loop boxing `UInt64` results
back into `Nat` via `lean_uint64_to_nat → lean_big_uint64_to_nat →
lean::mpz::mpz`. Inclusive own-code cost was led by
`Hex.GFqRing.reduceMod` (99.8%) →
`Hex.DensePoly.divModArray` (99.8%) →
`Hex.DensePoly.divModArrayAux` (99.7%) →
`Hex.DensePoly.subtractScaledShiftStep` (91.9%); per-coefficient
work appears as `Hex.ZMod64.mul` (44.9%), `Hex.ZMod64.sub` (42.0%),
and `Hex.ZMod64.complementWord` (37.9%). The dominant work maps to
the registered `runReduceModChecksum` target via the
`reduceMod → divModArray → subtractScaledShiftStep`
remainder-by-shift chain, exactly as the `n²` cost model predicts.

### `quotient-arithmetic`

Command:

```sh
lake exe hexgfqring_bench profile Hex.GFqRingBench.runMulChecksum \
    --param 256 --target-inner-nanos 5000000000 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        -o /tmp/hex-profiles/hex-gfq-ring-mul-28f9f6c95543.json --"
```

Representative case: deterministic dense `F_65537` canonical-rep
quotient pairs of size `n + 1 = 257` multiplied modulo the
deterministic dense modulus, parameter `n = 256`, no seed. Child
row: `inner_repeats=128`, `per_call_nanos=26001791.992188`,
`result_hash=0xeb5bd94c74ddcdcd`. Total `3363` non-empty samples.
Leaf samples were allocation/free 48.4%, Lean runtime 18.3%, GMP
16.4%, own code 6.3%, other 10.7%. Inclusive own-code cost split
between `Hex.GFqRing.mul → Hex.DensePoly.mul` (37.6%) for the
schoolbook product and `Hex.GFqRing.reduceMod →
Hex.DensePoly.divModArray → Hex.DensePoly.divModArrayAux` (62.1%
/ 62.2% / 62.1%) for the post-product remainder; the heavier
share is the reduction half because the dividend has degree
`2(n + 1)` after multiplication. Per-coefficient work appears as
`Hex.ZMod64.mul` (54.6%), `Hex.ZMod64.sub` (27.1%), and
`Hex.ZMod64.complementWord` (24.0%) inside
`subtractScaledShiftStep` (57.0%). The dominant work maps to the
registered `runMulChecksum` target via `GFqRing.mul` (the schoolbook
`DensePoly.mul`) followed by the same `GFqRing.reduceMod`
remainder chain measured in §dense-reduction, matching the `n²`
cost model: the multiplication and the reduction are both
`O(n²)` in the modulus degree, so combined throughput is also
`O(n²)`.

The dominant inclusive costs in both profiles all map to registered
`HexGfqRing/Bench.lean` targets. No unattributed dominant cost was
observed.

## Concerns
