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

Scientific run at commit `fa526bc19adb3aa4563f492025cbc99828572758` on
`carica` (Apple M2 Ultra, macOS 14.6.1), command:

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
  --export-file reports/bench-results/hex-matrix-mathlib-fa526bc19adb.json
```

The run used deterministic benchmark inputs from `HexMatrixMathlib/Bench.lean`;
random seeds are not involved. The harness recorded `fa526bc-dirty` because
this worktree had an unrelated pre-existing `.claude/CLAUDE.md` modification.
Export artefact: `reports/bench-results/hex-matrix-mathlib-fa526bc19adb.json`.

- `HexMatrixMathlib.MatrixBench.runMatrixEquivChecksum`: consistent with
  declared complexity (`β=-0.018`, parameters `128..512`, final hash
  `0x6100b605f6a40b5f`).
- `HexMatrixMathlib.MatrixBench.runMatrixEquivSymmChecksum`: consistent with
  declared complexity (`β=-0.011`, parameters `128..512`, final hash
  `0x321adb87757f9c6e`).
- `HexMatrixMathlib.MatrixBench.runRoundTripChecksum`: consistent with declared
  complexity (`β=-0.007`, parameters `128..512`, final hash
  `0x8c0691a0a585f5fb`).
- `HexMatrixMathlib.MatrixBench.runHexRowSwapBridgeChecksum`: consistent with
  declared complexity (`β=+0.014`, parameters `128..512`, final hash
  `0x7134908442c1e717`).
- `HexMatrixMathlib.MatrixBench.runMathlibRowSwapChecksum`: inconclusive;
  parameter `128` took `351.759 ms`, parameter `256` hit the `2.000 s`
  cap, and the final completed hash was `0x110b73e43abe004e`.
- `HexMatrixMathlib.MatrixBench.runHexRowScaleBridgeChecksum`: consistent with
  declared complexity (`β=+0.003`, parameters `128..512`, final hash
  `0x2d90eb89b083d4d6`).
- `HexMatrixMathlib.MatrixBench.runMathlibRowScaleChecksum`: inconclusive;
  parameter `256` took `1.525 s`, parameter `384` hit the `2.000 s` cap,
  and the final completed hash was `0xfd20a47b2fedd02d`.
- `HexMatrixMathlib.MatrixBench.runHexRowAddBridgeChecksum`: consistent with
  declared complexity (`β=+0.003`, parameters `128..512`, final hash
  `0x806e7f5b60b60f06`).
- `HexMatrixMathlib.MatrixBench.runMathlibRowAddChecksum`: inconclusive;
  parameter `256` took `1.897 s`, parameter `384` hit the `2.000 s` cap,
  and the final completed hash was `0xd0854176cf2ec674`.
- `HexMatrixMathlib.MatrixBench.runHexDetBridge`: consistent with declared
  complexity (`cMin=145.594`, `cMax=151.251`, parameters `3..7`, final hash
  `0xd56938f6cbe5da46`).
- `HexMatrixMathlib.MatrixBench.runMathlibDetBridge`: consistent with declared
  complexity (`cMin=620.881`, `cMax=721.354`, parameters `3..7`, final hash
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
at commit `fa526bc19adb3aa4563f492025cbc99828572758`; all reported
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
the Hex determinant bridge path at `n=7`. The direct Mathlib row-operation
targets were much slower than the executable bridge targets at `n=128`: about
`632x` for row swap, `360x` for row scale, and `425x` for row add. The hashes
agree, but the direct Mathlib row-operation targets are also the inconclusive
registrations listed in §Verdicts.

## Profile

Profiles were captured with `samply record --save-only --unstable-presymbolicate`
through the `lean-bench profile` subcommand at the same commit on `carica`
(Apple M2 Ultra, macOS 14.6.1). Sampling rate was samply's default 1000 Hz.
The raw Firefox Profiler JSON artefacts and sidecars are developer-local and
are not committed.

### `matrix-representation-conversion`

Command:

```sh
lake exe hexmatrixmathlib_bench profile HexMatrixMathlib.MatrixBench.runRoundTripChecksum --param 512 --profiler "samply record --save-only --unstable-presymbolicate --output /tmp/hex-profiles/hex-matrix-mathlib-conversion-fa526bc19adb.json.gz" --target-inner-nanos 3000000000
```

Representative case: deterministic dense integer matrix round trips, parameter
`512`, no seed. The child row reported `128` inner repeats, `2.629 s` total,
`20.541 ms` per call, and result hash `0x8c0691a0a585f5fb`. The profile shape
is dominated by conversion and checksum traversal over `n^2` entries, with
allocation and Lean runtime dispatch visible around the dense-vector and
function-matrix boundary. The dominant work maps to the registered conversion
and round-trip targets.

### `row-operation-bridge-checks`

Command:

```sh
lake exe hexmatrixmathlib_bench profile HexMatrixMathlib.MatrixBench.runMathlibRowAddChecksum --param 256 --profiler "samply record --save-only --unstable-presymbolicate --output /tmp/hex-profiles/hex-matrix-mathlib-rowop-fa526bc19adb.json.gz" --target-inner-nanos 3000000000 --max-seconds-per-call 4.0
```

Representative case: deterministic square integer matrix with the direct
Mathlib transvection row-add construction, parameter `256`, no seed. The child
row reported `1` inner repeat, `1.938 s` total, `1.938 s` per call, and result
hash `0xd0854176cf2ec674`. This is the same family as the Phase-4 blocker:
the direct Mathlib row-operation benchmark spends its dominant inclusive time
inside the generic Mathlib matrix multiplication/transvection path rather than
the executable Hex row-update path. Leaf cost is therefore classified primarily
as Lean runtime/allocation and Mathlib-side matrix work, with own
HexMatrixMathlib code limited to fixture construction, bridge conversion, and
checksum framing. The unresolved attribution/model concern is linked in
§Concerns.

### `determinant-bridge-checks`

Command:

```sh
lake exe hexmatrixmathlib_bench profile HexMatrixMathlib.MatrixBench.runMathlibDetBridge --param 7 --profiler "samply record --save-only --unstable-presymbolicate --output /tmp/hex-profiles/hex-matrix-mathlib-det-fa526bc19adb.json.gz" --target-inner-nanos 3000000000
```

Representative case: deterministic small integer matrix on the Mathlib
determinant bridge path, parameter `7`, no seed. The child row reported `64`
inner repeats, `1.904 s` total, `29.753 ms` per call, and result hash
`0xd56938f6cbe5da46`. Dominant inclusive work follows the registered Leibniz
determinant target; conversion is quadratic and does not dominate at this
schedule. Leaf cost is attributable to Lean runtime/allocation and integer
arithmetic in the determinant expansion, with no external GMP or comparator
component involved in this bridge benchmark.

## Concerns

- [#3147](https://github.com/kim-em/hex/issues/3147): direct Mathlib
  row-operation targets are inconclusive against their declared `n * n`
  complexity and hit the scientific wall-clock cap.
