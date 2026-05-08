# HexMatrix Performance Report

## Bench Targets

- `Hex.MatrixBench.runSquareMulChecksum`: `n * n * n`
- `Hex.MatrixBench.runBareissDet`: `n * n * n`
- `Hex.MatrixBench.runLeibnizDet`: `n * leibnizDetComplexity n`

## Verdicts

All scientific runs were made with `leanprover/lean4:4.30.0-rc2` on macOS
arm64 at commit `8341765f66f456b6b3c56e3d79065bbb92f1cf1d-dirty`. The dirty
bit is the pod-managed `.claude/CLAUDE.md` worktree change, not a benchmark
source change. The CLI emits the benchmark table and child JSONL row to stdout;
no JSONL file is written by the harness for these invocations.

- `Hex.MatrixBench.runSquareMulChecksum`
  - Command: `lake exe hexmatrix_bench run Hex.MatrixBench.runSquareMulChecksum`
  - Input family: `dense-square-multiplication`; deterministic salts `17` and
    `43`; parameters `160, 192, 224, 256`.
  - Per-call times: `450.179 ms`, `780.401 ms`, `1.238 s`, `1.849 s`.
  - Verdict: consistent with declared complexity (`cMin=109.907`,
    `cMax=110.259`, `β=—`).
- `Hex.MatrixBench.runBareissDet`
  - Command: `lake exe hexmatrix_bench run Hex.MatrixBench.runBareissDet`
  - Input family: `structured-bareiss-determinant`; deterministic salt `71`;
    parameters `8, 12, 16`.
  - Per-call times: `9.305 µs`, `28.790 µs`, `73.519 µs`.
  - Verdict: consistent with declared complexity (`cMin=16.661`,
    `cMax=18.175`, `β=—`).
- `Hex.MatrixBench.runLeibnizDet`
  - Command: `lake exe hexmatrix_bench run Hex.MatrixBench.runLeibnizDet`
  - Input family: `leibniz-small-determinant`; deterministic salt `71`;
    parameters `2, 3, 4, 5, 6, 7, 8`.
  - Per-call times: `602.000 ns`, `1.985 µs`, `8.497 µs`, `48.233 µs`,
    `329.322 µs`, `2.655 ms`, `23.676 ms`.
  - Verdict: consistent with declared complexity (`cMin=73.399`,
    `cMax=80.389`, `β=—`).

`lake exe hexmatrix_bench list` reported all three registrations above, and
`lake exe hexmatrix_bench verify` passed all three smoke checks.

## Comparator Ratios

`SPEC/Libraries/hex-matrix.md` does not name an external Phase-4 performance
comparator for `HexMatrix`. The only Phase-4 comparison surface is the
within-Lean determinant cross-check between row-pivoted Bareiss and the generic
Leibniz determinant on the small common structured domain.

Command:
`lake exe hexmatrix_bench compare Hex.MatrixBench.runBareissDet Hex.MatrixBench.runLeibnizDet --param-floor 8 --param-ceiling 8`

The harness reported that the declared custom schedules make the floor/ceiling
flags informational for these registrations, then compared their common
parameter domain. The common domain was `n=8`, and the result was
`agreement: all functions agree on common params`.

Both determinant registrations also returned stable hashes on their scientific
runs:

- `Hex.MatrixBench.runBareissDet`, `n=16`: `0x15e450ea`
- `Hex.MatrixBench.runLeibnizDet`, `n=8`: `0x6554`

No external comparator ratio is required or recorded.

## Profile

Profiles were captured with `samply record --save-only` through the
`hexmatrix_bench profile` subcommand on an Apple M2 Ultra running macOS 14.6.1.
Sampling rate was samply's default 1000 Hz. Raw profiler JSON artefacts are
developer-local and are not committed.

- `dense-square-multiplication`
  - Command: `lake exe hexmatrix_bench profile Hex.MatrixBench.runSquareMulChecksum --param 160 --profiler "samply record --save-only --output /tmp/hexmatrix-squaremul-160-long.json.gz" --target-inner-nanos 5000000000`
  - Child row: `inner_repeats=8`, `per_call_nanos=466293921.875000`,
    `result_hash=0x1f393709728b7e`.
  - Leaf cost: almost entirely Lean own code in the compiled benchmark/matrix
    multiplication loop; isolated Lean runtime and allocator samples were below
    one percent. No GMP symbols appeared.
  - Inclusive ranking: the benchmark wrapper and the matrix multiplication
    hot loop dominated. This is attributable to the registered
    `runSquareMulChecksum` target.
- `structured-bareiss-determinant`
  - Command: `lake exe hexmatrix_bench profile Hex.MatrixBench.runBareissDet --param 16 --profiler "samply record --save-only --output /tmp/hexmatrix-bareiss-16-long.json.gz" --target-inner-nanos 5000000000`
  - Child row: `inner_repeats=65536`, `per_call_nanos=76139.127090`,
    `result_hash=0x15e450ea`.
  - Leaf cost: almost entirely Lean own code in the compiled determinant loop;
    isolated Lean runtime and allocator samples were below one percent. No GMP
    symbols appeared on the small-entry structured family.
  - Inclusive ranking: the benchmark wrapper and Bareiss determinant path
    dominated. This is attributable to the registered `runBareissDet` target.
- `leibniz-small-determinant`
  - Command: `lake exe hexmatrix_bench profile Hex.MatrixBench.runLeibnizDet --param 8 --profiler "samply record --save-only --output /tmp/hexmatrix-leibniz-8-long.json.gz" --target-inner-nanos 5000000000`
  - Child row: `inner_repeats=128`, `per_call_nanos=24850669.273438`,
    `result_hash=0x6554`.
  - Leaf cost: almost entirely Lean own code in the compiled Leibniz
    permutation/fold loop; isolated Lean runtime and allocator samples were
    below one percent. No GMP symbols appeared.
  - Inclusive ranking: the benchmark wrapper and Leibniz determinant fold
    dominated. This is attributable to the registered `runLeibnizDet` target.

The dominant inclusive costs all map to registered `HexMatrix.Bench` targets.
No unattributed dominant cost was observed.

## Concerns
