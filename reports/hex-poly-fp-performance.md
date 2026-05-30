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

Scientific run at commit `cee076f68d9f` on `carica` (Apple M2 Ultra,
macOS 15.6, arm64), command:

```sh
lake exe hexpolyfp_bench run \
    Hex.FpPolyBench.runFrobeniusXModChecksum \
    Hex.FpPolyBench.runWeightedProductChecksum \
    Hex.FpPolyBench.runSquareFreeDecompositionSummary \
    Hex.FpPolyBench.runFrobeniusXPowModChecksum \
    Hex.FpPolyBench.runPowModMonicChecksum \
    Hex.FpPolyBench.runComposeModMonicChecksum \
    --export-file reports/bench-results/hex-poly-fp-cee076f68d9f.json
```

The run used deterministic fixtures from `HexPolyFp/Bench.lean`; no random
seeds are involved. The harness recorded `cee076f-dirty` because this
worktree had an unrelated pre-existing `.claude/CLAUDE.md` modification.
Export artefact: `reports/bench-results/hex-poly-fp-cee076f68d9f.json`,
SHA-256
`0f88c003092f8618a98263dd887b819c4f9dd9cf51cab66074fe1dec8ff3a29f`.

- `Hex.FpPolyBench.runFrobeniusXModChecksum`: consistent with declared
  complexity (`cMin=4477.355`, `cMax=5584.809`, `β=-0.184`, parameters
  `16,24,32,48,64,80`, `slopeTolerance=0.20`, final hash
  `0xac1417f1a37c7f40`).
- `Hex.FpPolyBench.runWeightedProductChecksum`: consistent with declared
  complexity (`cMin=187.827`, `cMax=190.969`, `β=-0.001`, parameters
  `256,384,512,768,1024,1536,2048,3072,4096`, final hash
  `0x972bd3a6f2b6d429`).
- `Hex.FpPolyBench.runSquareFreeDecompositionSummary`: consistent with
  declared complexity (`cMin=83.103`, `cMax=311.692`, `β=-0.235`,
  parameters `64,96,128,192,256,384,512,768`, `slopeTolerance=0.30`,
  final hash `0x66ff822aca96ce87`). The widened slope tolerance covers
  the fixture's bounded `n`-to-`n` constant variance: rungs whose balanced
  multiplicities divide `p = 5` take extra Yun shrink steps because those
  factors vanish from `f'`, while the fitted asymptote remains consistent
  with the declared `O(n^2)` model.
- `Hex.FpPolyBench.runFrobeniusXPowModChecksum`: consistent with declared
  complexity (`cMin=9739.644`, `cMax=10192.759`, parameters
  `16,24,32,48,64`, no cap-truncation advisory, final hash
  `0x6b9763a45f6b5d11`).
- `Hex.FpPolyBench.runPowModMonicChecksum`: consistent with declared
  complexity (`cMin=485.430`, `cMax=604.917`, `β=-0.075`, parameters
  `64,96,128,192,256,384,512`, final hash `0x3f65c86be5e72dd5`).
- `Hex.FpPolyBench.runComposeModMonicChecksum`: consistent with declared
  complexity (`cMin=398.802`, `cMax=414.557`, `β=-0.024`, parameters
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

Profiles were captured at commit
`3bc24c50fbe57487776c433106894ee544a6d656` with
`scripts/profile/run_profile.sh`, which drives `samply record --save-only
--no-open --rate 999 --unstable-presymbolicate` and filters the Firefox
Profiler JSON to samples from the benchmark thread during the bench library's
timed regions. The host was `carica` (Apple M2 Ultra, macOS 14.6.1, arm64);
`samply --version` reported `0.13.1`, and the bench child reported
`lean_bench_version=0.1.0`. The worktree was dirty only because
`.claude/CLAUDE.md` carried a pre-existing agent-context change outside this
report package. Raw filtered artefacts are developer-local under
`/tmp/hex-profile-*.json.gz` and are not committed. Percentages below are leaf
counts and inclusive counts as fractions of the retained bench-thread samples.

### `quotient-powers`

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexpolyfp_bench \
    Hex.FpPolyBench.runPowModMonicChecksum 512 1000000000
```

Representative case: dense `F_65537` quotient-ring square-and-multiply at
parameter `512`, no seed. Child row: `inner_repeats=1`,
`per_call_nanos=1187296834`, result hash `0x3f65c86be5e72dd5`. The filtered
profile retained `1186` bench-thread samples at
`/tmp/hex-profile-runPowModMonicChecksum-512.json.gz`.

Leaf samples were allocation/free `597 / 1186 = 50.3%`, Lean runtime
`221 / 1186 = 18.6%`, GMP big-integer arithmetic `164 / 1186 = 13.8%`,
other frames `128 / 1186 = 10.8%`, and own HexPolyFp/HexPoly/ZMod64 code
`76 / 1186 = 6.4%`. Top inclusive Hex costs were
`FpPoly.powModMonicAux` and `runPowModMonicChecksum` at
`1186 / 1186 = 100.0%`, `DensePoly.modByMonic`/`divModArrayAux` at
`738 / 1186 = 62.2%`, `DensePoly.subtractScaledShiftStep` at
`680 / 1186 = 57.3%`, `ZMod64.mul` at `648 / 1186 = 54.6%`, and
`DensePoly.mul` at `448 / 1186 = 37.8%`. The dominant inclusive path maps
directly to the
registered quotient-power target through square-and-multiply and dense
reduced multiplication.

Diagnostics block:

```text
bench thread:       name='Thread <4896685>' tid=4896685
regions:            1, total timed = 1187.3 ms
expected samples:   ~1186 on bench thread
retained samples:   1186 on bench thread (9 rejected outside windows)
other-thread noise: 2 samples on non-bench threads within timed windows (informational)
filtered profile:   /tmp/hex-profile-runPowModMonicChecksum-512.json.gz
spawn_anchor_wall_ns: 1780142640913444000
spawn_anchor_mono_ns: 330674834453916
sidecar_mono_anchor_ns: 330675785300833
samply_meta_start_time_ms: 1780142640920.905
```

### `modular-composition`

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexpolyfp_bench \
    Hex.FpPolyBench.runComposeModMonicChecksum 128 1000000000
```

Representative case: same-size dense `F_65537` modular composition at
parameter `128`, no seed. Child row: `inner_repeats=1`,
`per_call_nanos=861883333`, result hash `0x603f51d2369b957a`. The filtered
profile retained `861` bench-thread samples at
`/tmp/hex-profile-runComposeModMonicChecksum-128.json.gz`.

Leaf samples were allocation/free `419 / 861 = 48.7%`, Lean runtime
`163 / 861 = 18.9%`, GMP big-integer arithmetic `123 / 861 = 14.3%`,
other frames `99 / 861 = 11.5%`, and own HexPolyFp/HexPoly/ZMod64 code
`57 / 861 = 6.6%`. Top inclusive Hex costs were
`runComposeModMonicChecksum` at `861 / 861 = 100.0%`,
`DensePoly.modByMonic`/`divModArrayAux` at `536 / 861 = 62.3%`,
`DensePoly.subtractScaledShiftStep` at `503 / 861 = 58.4%`,
`ZMod64.mul` at `496 / 861 = 57.6%`, `FpPoly.composeModMonic`'s Horner step
at `325 / 861 = 37.7%`, and `DensePoly.mul` at `323 / 861 = 37.5%`.
The dominant inclusive work is the registered modular-composition quotient
path: Horner composition calling dense multiplication and monic reduction.

Diagnostics block:

```text
bench thread:       name='Thread <4903873>' tid=4903873
regions:            1, total timed = 861.9 ms
expected samples:   ~861 on bench thread
retained samples:   861 on bench thread (9 rejected outside windows)
other-thread noise: 2 samples on non-bench threads within timed windows (informational)
filtered profile:   /tmp/hex-profile-runComposeModMonicChecksum-128.json.gz
spawn_anchor_wall_ns: 1780142741021863000
spawn_anchor_mono_ns: 330774943970250
sidecar_mono_anchor_ns: 330775168830208
samply_meta_start_time_ms: 1780142741029.186
```

### `product-squarefree`

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexpolyfp_bench \
    Hex.FpPolyBench.runWeightedProductChecksum 2048 1000000000
```

Representative case: deterministic `F_5` product of `2048` linear factors, no
seed. Child row: `inner_repeats=1`, `per_call_nanos=795519959`, result hash
`0x90df9d7f9d6bed59`. The filtered profile retained `795` bench-thread
samples at `/tmp/hex-profile-runWeightedProductChecksum-2048.json.gz`.

Leaf samples were allocation/free `326 / 795 = 41.0%`, Lean runtime
`190 / 795 = 23.9%`, other frames `132 / 795 = 16.6%`,
own HexPolyFp/HexPoly/ZMod64 code `94 / 795 = 11.8%`, and GMP big-integer
arithmetic `53 / 795 = 6.7%`. Top inclusive Hex costs were
`runWeightedProductChecksum` at `795 / 795 = 100.0%`, `DensePoly.mul` at
`738 / 795 = 92.8%`, its coefficient loop at `604 / 795 = 76.0%`,
`ZMod64.mul` at `467 / 795 = 58.7%`, and `DensePoly.trimTrailingZeros` at
`31 / 795 = 3.9%`. The dominant work is attributable to the registered
weighted-product target and its expected linear-factor multiplication ladder.

Diagnostics block:

```text
bench thread:       name='Thread <4904332>' tid=4904332
regions:            1, total timed = 795.5 ms
expected samples:   ~795 on bench thread
retained samples:   795 on bench thread (8 rejected outside windows)
other-thread noise: 2 samples on non-bench threads within timed windows (informational)
filtered profile:   /tmp/hex-profile-runWeightedProductChecksum-2048.json.gz
spawn_anchor_wall_ns: 1780142749639888000
spawn_anchor_mono_ns: 330783562089333
sidecar_mono_anchor_ns: 330783783279375
samply_meta_start_time_ms: 1780142749647.64
```

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexpolyfp_bench \
    Hex.FpPolyBench.runSquareFreeDecompositionSummary 128 1000000000
```

Representative case: Yun square-free decomposition summary for a deterministic
`F_5` product built by `balancedSquareFreeFactors 128`, no seed. The
balanced multiplicity tuple is `(26, 26, 26, 25, 25)`. Child row:
`inner_repeats=128`, `per_call_nanos=5249734.375000`, result hash
`0xc190ee24ddc83ab8`. The filtered profile retained `677` bench-thread
samples at
`/tmp/hex-profile-runSquareFreeDecompositionSummary-128.json.gz`.

Leaf samples were Lean runtime `241 / 677 = 35.6%`, allocation/free
`221 / 677 = 32.6%`, own HexPolyFp/HexPoly/ZMod64 code
`83 / 677 = 12.3%`, other frames `74 / 677 = 10.9%`, and GMP big-integer
arithmetic `58 / 677 = 8.6%`. Top inclusive Hex costs were
`FpPoly.squareFreeDecomposition` at `676 / 677 = 99.9%`,
`FpPoly.squareFreeAuxRev` at `674 / 677 = 99.6%`,
`FpPoly.yunFactorsWithLevel` at `640 / 677 = 94.5%`,
`DensePoly.divModArray` at `536 / 677 = 79.2%`,
`DensePoly.gcd`/`DensePoly.xgcd` at `413 / 677 = 61.0%`, and
`DensePoly.div` at `256 / 677 = 37.8%`.
The sampled work maps to the registered square-free target through Yun's
gcd/division chain on the current balanced fixture.

Diagnostics block:

```text
bench thread:       name='Thread <4904649>' tid=4904649
regions:            2, total timed = 677.2 ms
expected samples:   ~677 on bench thread
retained samples:   677 on bench thread (10 rejected outside windows)
other-thread noise: 2 samples on non-bench threads within timed windows (informational)
filtered profile:   /tmp/hex-profile-runSquareFreeDecompositionSummary-128.json.gz
spawn_anchor_wall_ns: 1780142758316090000
spawn_anchor_mono_ns: 330792238386083
sidecar_mono_anchor_ns: 330792474817458
samply_meta_start_time_ms: 1780142758323.7869
```

Across all four profiles, every dominant inclusive cost maps to a registered
`Hex.FpPolyBench.*` target: quotient powers to `runPowModMonicChecksum`,
modular composition to `runComposeModMonicChecksum`, product construction to
`runWeightedProductChecksum`, and Yun square-free decomposition to
`runSquareFreeDecompositionSummary`. No unattributed dominant profile cost was
observed.

## Concerns

None.
