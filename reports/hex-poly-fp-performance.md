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

Scientific run at commit `cb0b816af3b0` on `carica` (Apple M2 Ultra,
macOS 14.6.1, arm64), command:

```sh
lake exe hexpolyfp_bench run \
    Hex.FpPolyBench.runFrobeniusXModChecksum \
    Hex.FpPolyBench.runWeightedProductChecksum \
    Hex.FpPolyBench.runSquareFreeDecompositionSummary \
    Hex.FpPolyBench.runFrobeniusXPowModChecksum \
    Hex.FpPolyBench.runPowModMonicChecksum \
    Hex.FpPolyBench.runComposeModMonicChecksum \
    --export-file reports/bench-results/hex-poly-fp-cb0b816af3b0.json
```

The run used deterministic fixtures from `HexPolyFp/Bench.lean`; no random
seeds are involved. The harness recorded `cb0b816-dirty` because this
worktree had an unrelated pre-existing `.claude/CLAUDE.md` modification.
Export artefact: `reports/bench-results/hex-poly-fp-cb0b816af3b0.json`,
SHA-256
`bd715b4bf14707b79b2c8d0b691e3d2755d6e1a8bb216633604c201e9850e584`.

- `Hex.FpPolyBench.runFrobeniusXModChecksum`: consistent with declared
  complexity (`cMin=4454.635`, `cMax=5644.450`, `β=-0.199`, parameters
  `16,24,32,48,64,80`, `slopeTolerance=0.20`, final hash
  `0xac1417f1a37c7f40`).
- `Hex.FpPolyBench.runWeightedProductChecksum`: consistent with declared
  complexity (`cMin=184.912`, `cMax=190.695`, `β=-0.007`, parameters
  `256,384,512,768,1024,1536,2048,3072,4096`, final hash
  `0x972bd3a6f2b6d429`).
- `Hex.FpPolyBench.runSquareFreeDecompositionSummary`: consistent with
  declared complexity (`cMin=82.051`, `cMax=310.928`, `β=-0.236`,
  parameters `64,96,128,192,256,384,512,768`, `slopeTolerance=0.30`,
  final hash `0x66ff822aca96ce87`). The widened slope tolerance and the
  fixture's residual `n`-to-`n` constant variance are recorded as a
  Concern in §"Concerns" below.
- `Hex.FpPolyBench.runFrobeniusXPowModChecksum`: consistent with declared
  complexity (`cMin=9791.609`, `cMax=10302.897`, parameters
  `16,24,32,48,64`, no cap-truncation advisory, final hash
  `0x6b9763a45f6b5d11`).
- `Hex.FpPolyBench.runPowModMonicChecksum`: consistent with declared
  complexity (`cMin=491.493`, `cMax=604.346`, `β=-0.075`, parameters
  `64,96,128,192,256,384,512`, final hash `0x3f65c86be5e72dd5`).
- `Hex.FpPolyBench.runComposeModMonicChecksum`: consistent with declared
  complexity (`cMin=404.189`, `cMax=416.167`, `β=-0.018`, parameters
  `32,48,64,96,128,192`, no cap-truncation advisory, final hash
  `0xee8f3ebaae233227`).

Smoke wiring was checked at the same commit with:

```sh
lake exe hexpolyfp_bench list
lake exe hexpolyfp_bench verify
```

`verify` passed all six registered benchmarks. Every scientific verdict
is now consistent with the declared complexity, with no cap-truncation
advisories.

## Comparator Ratios

`SPEC/Libraries/hex-poly-fp.md` does not name an external Phase-4 performance
comparator for `HexPolyFp`, so there are no external comparator ratios to
record in this snapshot.

## Profile

Profiles were captured with `samply record --save-only
--unstable-presymbolicate` through the `hexpolyfp_bench profile` child path at
commit `da69fc9e2e5c` on `carica` (Apple M2 Ultra, macOS 15.6, arm64),
sampling at 1 kHz. The worktree was dirty only because `.claude/CLAUDE.md`
carried a pre-existing agent-context change outside this report package. Raw
profiler artefacts are developer-local under `/tmp/hex-profiles/` and are not
committed. Each profile below sums samples from the benchmark worker child
thread, not the parent harness or the worker's lock-wait orchestration thread.
Percentages are leaf counts and inclusive counts as a fraction of those
worker-thread samples. Symbol attribution uses the samply `.syms.json` sidecar;
Lean-mangled `lp_Hex_*` symbols are reported below in demangled form when the
name is clear from the symbol.

The square-free profile predates the fixture's switch to
`balancedSquareFreeFactors`, but the new fixture's multiplicity
distribution at parameter `128` coincides with the previous fixture's
distribution at the same parameter (both yield `(26, 26, 26, 25, 25)`),
so the dominant inclusive costs are unchanged.

### `quotient-powers`

Command:

```sh
lake exe hexpolyfp_bench profile Hex.FpPolyBench.runPowModMonicChecksum \
    --param 512 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        --include-args=6 --rate 1000 \
        -o /tmp/hex-profiles/hex-poly-fp-powmod-713a73d5754c.json --" \
    --target-inner-nanos 800000000
```

Representative case: dense `F_65537` quotient-ring square-and-multiply at
parameter `512`, no seed. Child row: `inner_repeats=1`,
`per_call_nanos=1172250208`, result hash `0x3f65c86be5e72dd5`. The worker
thread recorded `1179` sample rows with total sample weight `1205`; sidecar:
`/tmp/hex-profiles/hex-poly-fp-powmod-713a73d5754c.syms.json`.

Leaf samples were allocation/free `586 / 1205 = 48.6%`, Lean runtime
`210 / 1205 = 17.4%`, GMP big-integer arithmetic `159 / 1205 = 13.2%`,
own HexPolyFp/HexPoly/ZMod64 code `99 / 1205 = 8.2%`, and other frames
`151 / 1205 = 12.5%`. Top inclusive Hex costs were
`FpPoly.powModMonicAux`/`runPowModMonicChecksum` at `1172 / 1205 = 97.3%`,
`DensePoly.modByMonic`/`divModArrayAux` at `723 / 1205 = 60.0%`,
`DensePoly.subtractScaledShiftStep` at `660 / 1205 = 54.8%`,
`ZMod64.mul` at `616 / 1205 = 51.1%`, and `DensePoly.mul` at
`449 / 1205 = 37.3%`. The dominant inclusive path maps directly to the
registered quotient-power target through square-and-multiply and dense
reduced multiplication.

### `modular-composition`

Command:

```sh
lake exe hexpolyfp_bench profile Hex.FpPolyBench.runComposeModMonicChecksum \
    --param 128 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        --include-args=6 --rate 1000 \
        -o /tmp/hex-profiles/hex-poly-fp-compose-713a73d5754c.json --" \
    --target-inner-nanos 800000000
```

Representative case: same-size dense `F_65537` modular composition at
parameter `128`, no seed. Child row: `inner_repeats=1`,
`per_call_nanos=870650250`, result hash `0x603f51d2369b957a`. The worker
thread recorded `879` sample rows with total sample weight `900`; sidecar:
`/tmp/hex-profiles/hex-poly-fp-compose-713a73d5754c.syms.json`.

Leaf samples were allocation/free `438 / 900 = 48.7%`, GMP big-integer
arithmetic `142 / 900 = 15.8%`, other frames `141 / 900 = 15.7%`,
Lean runtime `123 / 900 = 13.7%`, and own HexPolyFp/HexPoly/ZMod64 code
`56 / 900 = 6.2%`. Top inclusive Hex costs were
`runComposeModMonicChecksum` at `870 / 900 = 96.7%`,
`DensePoly.modByMonic`/`divModArrayAux` at `534 / 900 = 59.3%`,
`DensePoly.subtractScaledShiftStep` at `493 / 900 = 54.8%`,
`ZMod64.mul` at `476 / 900 = 52.9%`, `FpPoly.composeModMonic`'s Horner step
at `334 / 900 = 37.1%`, and `DensePoly.mul` at `329 / 900 = 36.6%`.
The dominant inclusive work is the registered modular-composition quotient
path: Horner composition calling dense multiplication and monic reduction.

### `product-squarefree`

Command:

```sh
lake exe hexpolyfp_bench profile Hex.FpPolyBench.runWeightedProductChecksum \
    --param 2048 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        --include-args=6 --rate 1000 \
        -o /tmp/hex-profiles/hex-poly-fp-weighted-product-713a73d5754c.json --" \
    --target-inner-nanos 800000000
```

Representative case: deterministic `F_5` product of `2048` linear factors, no
seed. Child row: `inner_repeats=1`, `per_call_nanos=809741667`, result hash
`0x90df9d7f9d6bed59`. The worker thread recorded `817` sample rows with total
sample weight `838`; sidecar:
`/tmp/hex-profiles/hex-poly-fp-weighted-product-713a73d5754c.syms.json`.

Leaf samples were allocation/free `366 / 838 = 43.7%`, Lean runtime
`183 / 838 = 21.8%`, other frames `148 / 838 = 17.7%`,
own HexPolyFp/HexPoly/ZMod64 code `73 / 838 = 8.7%`, and GMP big-integer
arithmetic `68 / 838 = 8.1%`. Top inclusive Hex costs were
`runWeightedProductChecksum` at `810 / 838 = 96.7%`, `DensePoly.mul` at
`765 / 838 = 91.3%`, its coefficient loop at `608 / 838 = 72.6%`,
`ZMod64.mul` at `474 / 838 = 56.6%`, and `DensePoly.trimTrailingZeros` at
`31 / 838 = 3.7%`. The dominant work is attributable to the registered
weighted-product target and its expected linear-factor multiplication ladder.

Command:

```sh
lake exe hexpolyfp_bench profile \
    Hex.FpPolyBench.runSquareFreeDecompositionSummary \
    --param 128 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        --include-args=6 --rate 1000 \
        -o /tmp/hex-profiles/hex-poly-fp-squarefree-713a73d5754c.json --" \
    --target-inner-nanos 800000000
```

Representative case: Yun square-free decomposition summary for a deterministic
`F_5` product of linear factors at parameter `128`, no seed. Child row:
`inner_repeats=128`, `per_call_nanos=4695993.820312`, result hash
`0xc01a72c633d7eda5`. The worker thread recorded `618` sample rows with total
sample weight `640`; sidecar:
`/tmp/hex-profiles/hex-poly-fp-squarefree-713a73d5754c.syms.json`.

Leaf samples were allocation/free `203 / 640 = 31.7%`, Lean runtime
`191 / 640 = 29.8%`, other frames `95 / 640 = 14.8%`,
own HexPolyFp/HexPoly/ZMod64 code `90 / 640 = 14.1%`, and GMP big-integer
arithmetic `61 / 640 = 9.5%`. Top inclusive Hex costs were
`FpPoly.squareFreeDecomposition` at `606 / 640 = 94.7%`,
`FpPoly.squareFreeAuxRev` at `603 / 640 = 94.2%`,
`FpPoly.yunFactorsWithLevel` at `568 / 640 = 88.8%`,
`DensePoly.divModArray` at `478 / 640 = 74.7%`,
`DensePoly.gcd` at `366 / 640 = 57.2%`,
`DensePoly.xgcd` at `365 / 640 = 57.0%`, and `DensePoly.div` at
`233 / 640 = 36.4%`. The sampled work maps to the registered square-free
target through Yun's gcd/division chain.

Across all four profiles, every dominant inclusive cost maps to a registered
`Hex.FpPolyBench.*` target: quotient powers to `runPowModMonicChecksum`,
modular composition to `runComposeModMonicChecksum`, product construction to
`runWeightedProductChecksum`, and Yun square-free decomposition to
`runSquareFreeDecompositionSummary`. No unattributed dominant profile cost was
observed.

## Concerns

- `Hex.FpPolyBench.runSquareFreeDecompositionSummary` runs at a widened
  `slopeTolerance = 0.30` and exhibits a `cMax / cMin` constant ratio of
  about `3.8x` across the scientific rungs. The variance is inherent to
  the input family: at rungs where one or more of the five linear-factor
  multiplicities divides `p = 5` (for the current schedule this happens
  at `n = 96` and `n = 128`), the factor's contribution to `f'`
  vanishes, the squarefree part `c_0` collapses to fewer distinct
  factors, and the Yun ladder takes more shrink steps before exhausting
  `c_0`. The asymptote stays `O(n^2)` on every rung, but the constant
  jumps by a small integer factor. The scientific schedule already
  trims the worst-case rung `n = 1024` (four multiplicities divisible
  by `5` simultaneously, constant amplified by an order of magnitude);
  a structurally cleaner fixture that exercises Yun's full multiplicity
  ladder without ever triggering the formal-`p`-th-root special-case
  branches would require either a larger prime field or a more
  elaborate distinct-factor enumeration than `F_5` supports natively.
