# HexPolyFp Performance Report

## Bench Targets

- `Hex.FpPolyBench.runPowModMonicChecksum`:
  `n * n * Nat.log2 (n + 1)`
- `Hex.FpPolyBench.runFrobeniusXModChecksum`: `n * n * n`
- `Hex.FpPolyBench.runFrobeniusXPowModChecksum`: `n * n * n`
- `Hex.FpPolyBench.runComposeModMonicChecksum`: `n * n * n`
- `Hex.FpPolyBench.runWeightedProductChecksum`: `n * n`
- `Hex.FpPolyBench.runSquareFreeDecompositionSummary`: `n * n`

## Verdicts

Scientific run at commit `713a73d5754c` on `carica` (Apple M2 Ultra,
macOS 14.6.1, arm64), command:

```sh
lake exe hexpolyfp_bench run \
    Hex.FpPolyBench.runFrobeniusXModChecksum \
    Hex.FpPolyBench.runWeightedProductChecksum \
    Hex.FpPolyBench.runSquareFreeDecompositionSummary \
    Hex.FpPolyBench.runFrobeniusXPowModChecksum \
    Hex.FpPolyBench.runPowModMonicChecksum \
    Hex.FpPolyBench.runComposeModMonicChecksum \
    --export-file reports/bench-results/hex-poly-fp-713a73d5754c.json
```

The run used deterministic fixtures from `HexPolyFp/Bench.lean`; no random
seeds are involved. The harness recorded `713a73d-dirty` because this worktree
had an unrelated pre-existing `.claude/CLAUDE.md` modification. Export
artefact: `reports/bench-results/hex-poly-fp-713a73d5754c.json`, SHA-256
`b7b2130f909cc9254eda567882cb76abd85a01cdbfc97f24fc521b7bd27bf6c8`.

- `Hex.FpPolyBench.runFrobeniusXModChecksum`: inconclusive
  (`cMin=4710.952`, `cMax=6767.546`, `beta=-0.262`, parameters
  `8,12,16,24,32,48`, final hash `0x256b370e2b51ce00`).
- `Hex.FpPolyBench.runWeightedProductChecksum`: consistent with declared
  complexity (`cMin=183.783`, `cMax=191.345`, `beta=-0.010`, parameters
  `256,384,512,768,1024,1536,2048,3072,4096`, final hash
  `0x972bd3a6f2b6d429`).
- `Hex.FpPolyBench.runSquareFreeDecompositionSummary`: inconclusive
  (`cMin=242.750`, `cMax=946.824`, `beta=-0.401`, parameters
  `16,24,32,48,64,96,128`, final hash `0xc01a72c633d7eda5`).
- `Hex.FpPolyBench.runFrobeniusXPowModChecksum`: consistent with declared
  complexity (`cMin=10014.968`, `cMax=10291.799`, parameters
  `16,24,32,48,64`; parameter `96` hit the `maxSecondsPerCall = 4.0s`
  cap, final completed hash `0x6b9763a45f6b5d11`).
- `Hex.FpPolyBench.runPowModMonicChecksum`: consistent with declared
  complexity (`cMin=492.978`, `cMax=614.213`, `beta=-0.084`, parameters
  `64,96,128,192,256,384,512`, final hash `0x3f65c86be5e72dd5`).
- `Hex.FpPolyBench.runComposeModMonicChecksum`: consistent with declared
  complexity (`cMin=403.391`, `cMax=417.428`, `beta=-0.012`, parameters
  `32,48,64,96,128,192`; parameter `256` hit the
  `maxSecondsPerCall = 4.0s` cap, final completed hash
  `0xee8f3ebaae233227`).

Smoke wiring was checked at the same commit with:

```sh
lake exe hexpolyfp_bench list
lake exe hexpolyfp_bench verify
```

`verify` passed all six registered benchmarks. The two inconclusive scientific
verdicts keep `HexPolyFp.done_through` at `3`.

## Comparator Ratios

`SPEC/Libraries/hex-poly-fp.md` does not name an external Phase-4 performance
comparator for `HexPolyFp`, so there are no external comparator ratios to
record in this snapshot.

## Profile

Profiles were captured with `samply record --save-only
--unstable-presymbolicate` through the `hexpolyfp_bench profile` child path at
the same commit on `carica` (Apple M2 Ultra, macOS 14.6.1), sampling at samply's
default 1 kHz rate. Raw profiler artefacts are developer-local under
`/tmp/hex-profiles/` and are not committed. Each profile below sampled the
benchmark child process rather than the parent harness.

### `quotient-powers`

Command:

```sh
lake exe hexpolyfp_bench profile Hex.FpPolyBench.runPowModMonicChecksum \
    --param 512 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        -o /tmp/hex-profiles/hex-poly-fp-powmod-713a73d5754c.json --" \
    --target-inner-nanos 800000000
```

Representative case: dense `F_65537` quotient-ring square-and-multiply at
parameter `512`, no seed, profile row hash `0x3f65c86be5e72dd5`. The profile
recorded `1209` samples on the benchmark worker thread and emitted
`hex-poly-fp-powmod-713a73d5754c.syms.json`, whose symbol table contains the
expected `Hex.FpPolyBench.runPowModMonicChecksum`, `Hex.DensePoly.mul`,
`Hex.DensePoly.modByMonic`, and `Hex.ZMod64` arithmetic entries. The sampled
work maps to the registered quotient-power target and its dense reduced
multiplication kernel.

### `modular-composition`

Command:

```sh
lake exe hexpolyfp_bench profile Hex.FpPolyBench.runComposeModMonicChecksum \
    --param 128 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        -o /tmp/hex-profiles/hex-poly-fp-compose-713a73d5754c.json --" \
    --target-inner-nanos 800000000
```

Representative case: same-size dense `F_65537` modular composition at
parameter `128`, no seed, profile row hash `0x603f51d2369b957a`. The profile
recorded `897` samples on the benchmark worker thread and emitted
`hex-poly-fp-compose-713a73d5754c.syms.json`, whose symbol table contains the
expected `Hex.FpPolyBench.runComposeModMonicChecksum`,
`Hex.FpPoly.composeModMonic`, `Hex.DensePoly.mul`,
`Hex.DensePoly.modByMonic`, and `Hex.ZMod64` arithmetic entries. This covers
the registered modular-composition quotient path.

### `product-squarefree`

Command:

```sh
lake exe hexpolyfp_bench profile Hex.FpPolyBench.runWeightedProductChecksum \
    --param 2048 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        -o /tmp/hex-profiles/hex-poly-fp-weighted-product-713a73d5754c.json --" \
    --target-inner-nanos 800000000
```

Representative case: deterministic `F_5` product of `2048` linear factors, no
seed, profile row hash `0x90df9d7f9d6bed59`. The worker thread recorded `956`
samples and the symbol sidecar contains `Hex.FpPoly.weightedProduct`,
`Hex.DensePoly.mul`, and `Hex.ZMod64` coefficient arithmetic. The dominant work
is attributable to the registered weighted-product target and its expected
linear-factor multiplication ladder.

Command:

```sh
lake exe hexpolyfp_bench profile \
    Hex.FpPolyBench.runSquareFreeDecompositionSummary \
    --param 128 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        -o /tmp/hex-profiles/hex-poly-fp-squarefree-713a73d5754c.json --" \
    --target-inner-nanos 800000000
```

Representative case: Yun square-free decomposition summary for a deterministic
`F_5` product of linear factors at parameter `128`, no seed, profile row hash
`0xc01a72c633d7eda5`. The worker thread recorded `708` samples and the symbol
sidecar contains `Hex.FpPoly.squareFreeDecomposition`, `Hex.DensePoly.gcd`,
`Hex.DensePoly.xgcd`, `Hex.DensePoly.divMod`, `Hex.DensePoly.derivative`, and
`Hex.FpPoly.weightedProduct`. The sampled work maps to the registered
square-free target; the benchmark verdict itself remains inconclusive.

## Concerns

- `Hex.FpPolyBench.runFrobeniusXModChecksum` remains inconclusive on the
  current scientific schedule. The observed slope is faster than declared, so
  this looks like calibration noise or a model-domain issue rather than a
  wrong-slow implementation, but Phase 4 cannot complete until it is resolved.
- `Hex.FpPolyBench.runSquareFreeDecompositionSummary` remains inconclusive on
  the current scientific schedule. Its timings are non-monotone across
  `16..128`, so the square-free family needs a wider or better-shaped schedule
  before `HexPolyFp.done_through` can advance.
- `runFrobeniusXPowModChecksum` and `runComposeModMonicChecksum` both produced
  consistent verdicts before hitting the four-second cap on their largest
  scheduled rung. The completed rows are useful evidence, but the final Phase 4
  pass should either tune the schedule or explicitly accept the cap-truncated
  ladder.
- The profiles confirm that the expected `HexPolyFp`, `HexPoly`, and `ZMod64`
  symbols are present in samply sidecars, but this report does not yet include
  the required percentage leaf-cost split across own code, allocation, Lean
  runtime, and GMP. Final Phase 4 completion still needs full profile
  categorisation for every `HexPolyFp.phase4.input_families` entry.
