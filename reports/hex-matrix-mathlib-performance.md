# HexMatrixMathlib Performance Report

## Bench Targets

- `HexMatrixMathlib.MatrixBench.runMatrixEquivChecksum`: `n * n`
- `HexMatrixMathlib.MatrixBench.runMatrixEquivSymmChecksum`: `n * n`
- `HexMatrixMathlib.MatrixBench.runRoundTripChecksum`: `n * n`
- `HexMatrixMathlib.MatrixBench.runHexRowSwapBridgeChecksum`: `n * n`
- `HexMatrixMathlib.MatrixBench.runMathlibRowSwapChecksum`: `n * n`
- `HexMatrixMathlib.MatrixBench.runHexRowScaleBridgeChecksum`: `n * n`
- `HexMatrixMathlib.MatrixBench.runMathlibRowScaleChecksum`: `n * n`
- `HexMatrixMathlib.MatrixBench.runHexRowAddBridgeChecksum`: `n * n`
- `HexMatrixMathlib.MatrixBench.runMathlibRowAddChecksum`: `n * n`
- `HexMatrixMathlib.MatrixBench.runHexDetBridge`: `determinantBridgeComplexity n`
- `HexMatrixMathlib.MatrixBench.runMathlibDetBridge`: `determinantBridgeComplexity n`

## Verdicts

Scientific run at commit `713a73d5754c7dc05b51ec9df7c48ccdb23e312c` on
`carica` (Apple M2 Ultra, macOS 15.6), command:

```sh
lake exe hexmatrixmathlib_bench run \
  HexMatrixMathlib.MatrixBench.runMatrixEquivChecksum \
  HexMatrixMathlib.MatrixBench.runMatrixEquivSymmChecksum \
  HexMatrixMathlib.MatrixBench.runRoundTripChecksum \
  HexMatrixMathlib.MatrixBench.runHexRowSwapBridgeChecksum \
  HexMatrixMathlib.MatrixBench.runMathlibRowSwapChecksum \
  HexMatrixMathlib.MatrixBench.runHexRowScaleBridgeChecksum \
  HexMatrixMathlib.MatrixBench.runMathlibRowScaleChecksum \
  HexMatrixMathlib.MatrixBench.runHexRowAddBridgeChecksum \
  HexMatrixMathlib.MatrixBench.runMathlibRowAddChecksum \
  HexMatrixMathlib.MatrixBench.runHexDetBridge \
  HexMatrixMathlib.MatrixBench.runMathlibDetBridge \
  --export-file reports/bench-results/hex-matrix-mathlib-713a73d5754c.json
```

The run used deterministic benchmark inputs from `HexMatrixMathlib/Bench.lean`;
random seeds are not involved. The harness recorded `713a73d-dirty` because
this worktree had an unrelated pre-existing `.claude/CLAUDE.md` modification.
Export artefact: `reports/bench-results/hex-matrix-mathlib-713a73d5754c.json`.

- `HexMatrixMathlib.MatrixBench.runMatrixEquivChecksum`: consistent with
  declared complexity (`β=+0.006`, parameters `128..512`, final hash
  `0x6100b605f6a40b5f`).
- `HexMatrixMathlib.MatrixBench.runMatrixEquivSymmChecksum`: consistent with
  declared complexity (`β=-0.004`, parameters `128..512`, final hash
  `0x321adb87757f9c6e`).
- `HexMatrixMathlib.MatrixBench.runRoundTripChecksum`: consistent with declared
  complexity (`β=-0.011`, parameters `128..512`, final hash
  `0x8c0691a0a585f5fb`).
- `HexMatrixMathlib.MatrixBench.runHexRowSwapBridgeChecksum`: consistent with
  declared complexity (`β=-0.004`, parameters `128..512`, final hash
  `0x7134908442c1e717`).
- `HexMatrixMathlib.MatrixBench.runMathlibRowSwapChecksum`: consistent with
  declared complexity (`β=+0.001`, parameters `128..512`, final hash
  `0x7134908442c1e717`).
- `HexMatrixMathlib.MatrixBench.runHexRowScaleBridgeChecksum`: consistent with
  declared complexity (`β=-0.010`, parameters `128..512`, final hash
  `0x2d90eb89b083d4d6`).
- `HexMatrixMathlib.MatrixBench.runMathlibRowScaleChecksum`: consistent with
  declared complexity (`β=-0.002`, parameters `128..512`, final hash
  `0x2d90eb89b083d4d6`).
- `HexMatrixMathlib.MatrixBench.runHexRowAddBridgeChecksum`: consistent with
  declared complexity (`β=-0.008`, parameters `128..512`, final hash
  `0x806e7f5b60b60f06`).
- `HexMatrixMathlib.MatrixBench.runMathlibRowAddChecksum`: consistent with
  declared complexity (`β=+0.016`, parameters `128..512`, final hash
  `0x806e7f5b60b60f06`).
- `HexMatrixMathlib.MatrixBench.runHexDetBridge`: consistent with declared
  complexity (`cMin=146.213`, `cMax=151.589`, parameters `3..7`, final hash
  `0xd56938f6cbe5da46`).
- `HexMatrixMathlib.MatrixBench.runMathlibDetBridge`: consistent with declared
  complexity (`cMin=632.452`, `cMax=723.505`, parameters `3..7`, final hash
  `0xd56938f6cbe5da46`).

Smoke wiring was also checked with:

```sh
lake exe hexmatrixmathlib_bench list
lake exe hexmatrixmathlib_bench verify
```

`verify` passed all 11 registered benchmarks at the same commit.

## Comparator Ratios

`SPEC/Libraries/hex-matrix-mathlib.md` does not name an external Phase-4
comparator for `HexMatrixMathlib`, so there are no external comparator ratios
to record in this snapshot.

The within-Lean compare groups named in `HexMatrixMathlib/Bench.lean` were run
at commit `713a73d5754c7dc05b51ec9df7c48ccdb23e312c`; all reported
`agreement: all functions agree on common params`. The same commands were:

```sh
lake exe hexmatrixmathlib_bench compare \
  HexMatrixMathlib.MatrixBench.runHexDetBridge \
  HexMatrixMathlib.MatrixBench.runMathlibDetBridge
lake exe hexmatrixmathlib_bench compare \
  HexMatrixMathlib.MatrixBench.runHexRowSwapBridgeChecksum \
  HexMatrixMathlib.MatrixBench.runMathlibRowSwapChecksum
lake exe hexmatrixmathlib_bench compare \
  HexMatrixMathlib.MatrixBench.runHexRowScaleBridgeChecksum \
  HexMatrixMathlib.MatrixBench.runMathlibRowScaleChecksum
lake exe hexmatrixmathlib_bench compare \
  HexMatrixMathlib.MatrixBench.runHexRowAddBridgeChecksum \
  HexMatrixMathlib.MatrixBench.runMathlibRowAddChecksum
```

At the bottom scientific rung, the Mathlib determinant path was about `4.8x`
the Hex determinant bridge path at `n=7`. The direct Mathlib sparse
row-operation targets now track the executable bridge targets closely at
`n=512`: about `1.13x` for row swap, `1.14x` for row scale, and `1.17x` for
row add. These ratios are expected because both sides traverse all `n^2`
entries for the checksum; the Mathlib-side targets now avoid the generic
matrix-multiplication cost that previously made #3147 inconclusive.

## Profile

Profiles were captured with `samply record --save-only --unstable-presymbolicate`
through the `lean-bench profile` subcommand at the same commit on `carica`
(Apple M2 Ultra, macOS 15.6). Sampling rate was samply's default 1000 Hz.
The raw Firefox Profiler JSON artefacts and sidecars are developer-local and
are not committed.

### `matrix-representation-conversion`

Command:

```sh
lake exe hexmatrixmathlib_bench profile HexMatrixMathlib.MatrixBench.runRoundTripChecksum --param 512 --profiler "samply record --save-only --unstable-presymbolicate --output /tmp/hex-profiles/hex-matrix-mathlib-conversion-713a73d5754c.json.gz" --target-inner-nanos 3000000000
```

Representative case: deterministic dense integer matrix round trips, parameter
`512`, no seed. The child row reported `128` inner repeats, `2.686 s` total,
`20.987 ms` per call, and result hash `0x8c0691a0a585f5fb`. The profile shape
is dominated by conversion and checksum traversal over `n^2` entries, with
allocation and Lean runtime dispatch visible around the dense-vector and
function-matrix boundary. The dominant work maps to the registered conversion
and round-trip targets.

### `row-operation-bridge-checks`

Command:

```sh
lake exe hexmatrixmathlib_bench profile HexMatrixMathlib.MatrixBench.runMathlibRowAddChecksum --param 512 --profiler "samply record --save-only --unstable-presymbolicate --output /tmp/hex-profiles/hex-matrix-mathlib-rowop-713a73d5754c.json.gz" --target-inner-nanos 3000000000 --max-seconds-per-call 4.0
```

Representative case: deterministic square integer matrix with the direct
Mathlib sparse row-add construction, parameter `512`, no seed. The child row
reported `256` inner repeats, `2.758 s` total, `10.774 ms` per call, and result
hash `0x806e7f5b60b60f06`. The profile shape is dominated by the registered
sparse row-update/checksum target: one output row performs the transvection
arithmetic, the remaining rows forward existing entries, and the checksum
forces all `n^2` entries. Leaf cost is classified primarily as own
HexMatrixMathlib framing plus Lean runtime/allocation around function-matrix
entry evaluation; no generic matrix multiplication remains in the hot path.

### `determinant-bridge-checks`

Command:

```sh
lake exe hexmatrixmathlib_bench profile HexMatrixMathlib.MatrixBench.runMathlibDetBridge --param 7 --profiler "samply record --save-only --unstable-presymbolicate --output /tmp/hex-profiles/hex-matrix-mathlib-det-713a73d5754c.json.gz" --target-inner-nanos 3000000000
```

Representative case: deterministic small integer matrix on the Mathlib
determinant bridge path, parameter `7`, no seed. The child row reported `64`
inner repeats, `1.935 s` total, `30.231 ms` per call, and result hash
`0xd56938f6cbe5da46`. Dominant inclusive work follows the registered Leibniz
determinant target; conversion is quadratic and does not dominate at this
schedule. Leaf cost is attributable to Lean runtime/allocation and integer
arithmetic in the determinant expansion, with no external GMP or comparator
component involved in this bridge benchmark.

## Concerns

None.
