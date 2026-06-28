# HexMatrix Performance Report

## Bench Targets

- `Hex.MatrixBench.runSquareMulChecksum`: `n * n * n`
- `Hex.MatrixBench.runBareissDet`: `n * n * n`
- `Hex.MatrixBench.runLeibnizDet`: `n * leibnizDetComplexity n`

Paired Hex/FLINT informational comparator fixed registrations:
`runBareissDet{16,24,32,48,64,96,128,192,256,320,384,512}` ↔
`runFlintBareissDet{…}` (`fmpz_mat.det` via the shared persistent-
subprocess python-flint driver, per
`SPEC/Libraries/hex-matrix.md §"External comparators"` and
`SPEC/benchmarking.md §"External comparators" §"Process call"`).

## Verdicts

Scientific run at commit `77870fc99995a60f33a16a24ceca67c024b68f23` on
`carica` (Apple M2 Ultra, macOS 14.6.1), running every registered
parametric target plus every paired Hex/FLINT fixed comparator rung:

```sh
lake exe hexmatrix_bench run $(lake exe hexmatrix_bench list | awk '/^  Hex\./ {print $1}') \
    --export-file reports/bench-results/hex-matrix-77870fc.json
```

The harness recorded `77870fc-dirty` because this worktree carries the
pod-managed `.claude/CLAUDE.md` change plus the in-flight HO-25
`HexMatrix/Bench.lean` and `libraries.yml` additions. Export artefact:
`reports/bench-results/hex-matrix-77870fc.json`.

- `Hex.MatrixBench.runSquareMulChecksum`
  - Command: `lake exe hexmatrix_bench run Hex.MatrixBench.runSquareMulChecksum`
  - Input family: `dense-square-multiplication`; deterministic salts `17` and
    `43`; parameters `160, 192, 224, 256`.
  - Per-call times: `442.607 ms`, `763.753 ms`, `1.210 s`, `1.833 s`.
  - Verdict: consistent with declared complexity (`cMin=107.634`,
    `cMax=109.279`, `β=—`).
- `Hex.MatrixBench.runBareissDet`
  - Command: `lake exe hexmatrix_bench run Hex.MatrixBench.runBareissDet`
  - Input family: `structured-bareiss-determinant`; deterministic salt `71`;
    parameters `8, 12, 16`.
  - Per-call times: `9.136 µs`, `28.275 µs`, `72.236 µs`.
  - Verdict: consistent with declared complexity (`cMin=16.363`,
    `cMax=17.846`, `β=—`).
- `Hex.MatrixBench.runLeibnizDet`
  - Command: `lake exe hexmatrix_bench run Hex.MatrixBench.runLeibnizDet`
  - Input family: `leibniz-small-determinant`; deterministic salt `71`;
    parameters `2, 3, 4, 5, 6, 7, 8`.
  - Per-call times: `≤1 µs`, `1.957 µs`, `8.424 µs`, `47.000 µs`,
    `321.418 µs`, `2.566 ms`, `23.174 ms`.
  - Verdict: consistent with declared complexity (`cMin=71.843`,
    `cMax=78.334`, `β=—`).

The 24 paired Hex / FLINT fixed-comparator registrations also passed —
each Hex target and its paired FLINT call returned the same observed
hash at every rung (every `setup_fixed_benchmark` pair appears as a
`"hashes_agree": true` entry in the export). The agreement covers both
the magnitude and the sign of the determinant: Hex's row-pivoted
Bareiss tracks the swap permutation parity, and FLINT's multimodular
CRT returns the signed determinant in the same convention.

Smoke wiring was also checked with:

```sh
lake exe hexmatrix_bench list
lake exe hexmatrix_bench verify
```

`verify` passed all 27 registered benchmarks at the same commit (3
parametric + 24 paired fixed comparator rungs).

## Comparator Ratios

`SPEC/Libraries/hex-matrix.md §"External comparators"` names
`FLINT fmpz_mat_det via python-flint` (matching
`libraries.yml: HexMatrix.phase4.comparators[0].tool`) as the
`informational` external comparator for HexMatrix, scoped to the
determinant-surface bench targets (`runBareissDet` and equivalents).
The other Phase-4 matrix surfaces (`runSquareMulChecksum`, row
operations on the structural `Vector` / `Array` primitives) declare
absence with the `structural-layer` reason per the same SPEC
subsection. The comparator is wired through
`Hex.BenchOracle.Flint.runOp` against the shared persistent-subprocess
python-flint driver (`scripts/oracle/flint_bench_driver.py`, HO-20),
which already exposes `fmpz_mat.det`; HO-25 consumes the existing
op rather than extending the driver. The pairing is one-to-one:
`runBareissDet` ↔ `fmpz_mat.det`. `runSquareMulChecksum` and
`runLeibnizDet` have no FLINT pairing — `fmpz_mat` does not expose a
schoolbook-cubic multiplication entry point comparable to
`runSquareMulChecksum`, and Leibniz on a small structured domain is a
within-Lean cross-check (see the next paragraph), not an external
comparator.

A within-Lean determinant cross-check between `runBareissDet` and
`runLeibnizDet` remains available:

```sh
lake exe hexmatrix_bench compare Hex.MatrixBench.runBareissDet Hex.MatrixBench.runLeibnizDet --param-floor 8 --param-ceiling 8
```

The harness reports that the declared custom schedules make the
floor/ceiling flags informational for these registrations, then
compares the common parameter domain (`n=8`, result
`agreement: all functions agree on common params`). Both determinant
registrations also returned stable hashes on their scientific runs
(`Hex.MatrixBench.runBareissDet`, `n=16`: `0x15e450ea`;
`Hex.MatrixBench.runLeibnizDet`, `n=8`: `0x6554`).

### Per-call overhead

FLINT per-call overhead is measured by timing one driver spawn plus
one trivial `fmpz_mat.det` request on a `2×2` matrix
(`scripts/oracle/flint_bench_driver.py` invoked via
`/tmp/flint-overhead-measure.py`, 11 spawns on the same host):
median **55.2 ms**, min 53.7 ms, max 57.9 ms. The figure agrees with
HO-22's `fmpz_poly.add` measurement (56.3 ms median) — the driver
shape is identical across families, so the per-call overhead is a
single number per host, not per family. The `setup_fixed_benchmark`
shape spawns one bench child per repeat, so every FLINT median below
includes one driver startup. The `adjusted ratio` column subtracts
this overhead from the FLINT median when positive, then divides by
the Hex median. A rung is **eligible** under
`SPEC/benchmarking.md §"Headline reports" §"Comparator ratios"`
when (a) the 55.2 ms overhead is at most 50% of measured FLINT wall
time on that rung and (b) per-call wall time is at most the 10 s hard
ceiling.

### FLINT `fmpz_mat.det` vs `runBareissDet`

Input family `structured-bareiss-determinant`, declared complexity
`n³`. Hex's row-pivoted Bareiss fraction-free elimination against
FLINT's multimodular reduction + CRT determinant on the same
deterministic tridiagonal `flatSmallMatrix` fixture.

| n | Hex median | FLINT median | raw ratio | adjusted ratio | eligible |
|---:|---:|---:|---:|---:|:---:|
| 16 | 75.315 µs | 51.750 ms | 687.118x | 0.000x | no |
| 24 | 274.823 µs | 51.305 ms | 186.685x | 0.000x | no |
| 32 | 687.666 µs | 51.755 ms | 75.260x | 0.000x | no |
| 48 | 2.483 ms | 52.133 ms | 21.000x | 0.000x | no |
| 64 | 6.343 ms | 52.556 ms | 8.286x | 0.000x | no |
| 96 | 24.315 ms | 56.703 ms | 2.332x | 0.061x | no |
| 128 | 59.993 ms | 58.395 ms | 0.973x | 0.053x | no |
| 192 | 211.724 ms | 70.594 ms | 0.333x | 0.073x | no |
| 256 | 520.158 ms | 88.929 ms | 0.171x | 0.065x | no |
| 320 | 1.035 s | 114.064 ms | 0.110x | 0.057x | yes |
| 384 | 1.816 s | 149.450 ms | 0.082x | 0.052x | yes |
| 512 | 4.388 s | 270.629 ms | 0.062x | 0.049x | yes |

Trend: raw ratio falls monotonically across the entire ladder from
687x at `n = 16` (Hex is fast, FLINT is dominated by the ~55 ms
startup floor) through unity at `n = 128` to 0.062x at `n = 512`
(FLINT is more than sixteen times faster than Hex on wall time). Within
the three eligible rungs at the top of the ladder (`n = 320, 384,
512`) the adjusted ratio is essentially flat in the range
`0.049x – 0.057x` with a slow trend toward FLINT pulling further
ahead: once driver startup is subtracted, FLINT spends about 5% of
Hex's wall time on the same determinant surface, with the gap
widening as `n` grows. This is the structural gap
`SPEC/Libraries/hex-matrix.md §"External comparators"`'s
`informational` rationale named in advance (FLINT uses multimodular
reduction + CRT, Hex uses Bareiss fraction-free elimination); the
adverse trend is filed as the first Concern below. The comparator is
`informational`, so the divergence does not produce a gating-goal
verdict, but it is recorded here per
`SPEC/benchmarking.md §"Headline reports" §"Comparator ratios"`
("a diverging trend … is itself an audit-found Concern even when the
highest-rung verdict happens to pass").

The parametric `runBareissDet` schedule (`paramSchedule := .custom
#[8, 12, 16]`) is unchanged — the densification lives entirely in
the fixed-comparator ladder above per `SPEC/benchmarking.md
§"Headline reports" §"Comparator ratios"` ("the ladder is densified
with in-fill rungs between existing points, never extended past the
wallclock ceiling"). The top rung (`n = 512`, Hex 4.388 s) sits well
inside the 10 s hard per-call ceiling and the wider ladder gives
twelve points across roughly six orders of magnitude in measured Hex
wall time, enough to read the trend cleanly.

## Profile

Profiles were captured at commit
`3bc24c50fbe57487776c433106894ee544a6d656` on `carica` (Apple M2 Ultra,
macOS 14.6.1, arm64) through the bench-timed-region filtering wrapper:
`scripts/profile/run_profile.sh ./.lake/build/bin/hexmatrix_bench <target>
<param> 5000000000`. `samply 0.13.1` recorded at 999 Hz
(`--rate 999 --unstable-presymbolicate`), the bench binary reported
`lean-bench` version `0.1.0` on Lean `4.30.0-rc2`, and raw
`*.json.gz` artefacts remain developer-local under `/tmp`. The bench
child reported `git_dirty=true` because this pod worktree carried a
pod-managed `.claude/CLAUDE.md` change during capture.

- `dense-square-multiplication`
  - Command: `scripts/profile/run_profile.sh ./.lake/build/bin/hexmatrix_bench Hex.MatrixBench.runSquareMulChecksum 160 5000000000`
  - Child row: `inner_repeats=8`, `per_call_nanos=469770166.750000`,
    `result_hash=0x1f393709728b7e`.
  - Leaf cost: allocation/free 55.3%, Lean runtime and harness 24.7%,
    GMP big-integer arithmetic 15.1%, Lean own code 3.1%, other system
    samples 1.8%. The largest leaves were allocator/refcount paths
    (`libsystem_malloc`, `mi_malloc_small`, `mi_free`, `lean_dec_ref_cold`)
    plus GMP integer construction/comparison/copying in the `Int` dot-product
    loop.
  - Inclusive ranking: `Hex.MatrixBench.runSquareMulChecksum` and its
    benchmark wrapper covered 100.0% of retained samples,
    `Hex.Matrix.mul` specialised for the target covered 99.1%,
    `Hex.Vector.dotProduct` covered 93.8%, and the inner dot-product fold
    covered 82.0%. The high allocator/GMP leaf cost is therefore attributable
    to the registered `runSquareMulChecksum` target's boxed `Int` matrix
    multiplication surface.
  - Diagnostics:
    ```text
    bench thread:       name='Thread <4893104>' tid=4893104
    regions:            2, total timed = 4227.0 ms
    expected samples:   ~4223 on bench thread
    retained samples:   4219 on bench thread (15 rejected outside windows)
    other-thread noise: 2 samples on non-bench threads within timed windows (informational)
    spawn anchor:       wall_ns=1780142601187822000, mono_ns=330635108396541
    sidecar anchor:     mono_ns=330636312950125
    filtered profile:   /tmp/hex-profile-runSquareMulChecksum-160.json.gz
    ```
- `structured-bareiss-determinant`
  - Command: `scripts/profile/run_profile.sh ./.lake/build/bin/hexmatrix_bench Hex.MatrixBench.runBareissDet 16 5000000000`
  - Child row: `inner_repeats=32768`, `per_call_nanos=81462.912231`,
    `result_hash=0x15e450ea`.
  - Leaf cost: Lean runtime and harness 57.8%, Lean own code 22.6%,
    allocation/free 13.5%, GMP big-integer arithmetic 5.5%, other system
    samples 0.6%. The largest leaves were closure dispatch
    (`lean_apply_2`, `lean_apply_1`), `Hex.Matrix.stepMatrix` closures,
    `Array.ofFn` construction, `lean_array_push`, and exact-division support
    (`Int.decidableDvd`, `Hex.Matrix.exactDiv`).
  - Inclusive ranking: `Hex.Matrix.bareiss` covered 95.8% of retained samples,
    `bareissArrayState` covered 95.6%, `pivotLoop` covered 92.5%,
    `stepMatrix` covered 42.9% boxed / 36.5% unboxed, and
    `exactDiv` covered 8.1%. These dominant entries are the row-pivoted
    Bareiss determinant path measured by the registered `runBareissDet`
    target.
  - Diagnostics:
    ```text
    bench thread:       name='Thread <4894239>' tid=4894239
    regions:            9, total timed = 2693.9 ms
    expected samples:   ~2691 on bench thread
    retained samples:   2691 on bench thread (10 rejected outside windows)
    other-thread noise: 2 samples on non-bench threads within timed windows (informational)
    spawn anchor:       wall_ns=1780142613300175000, mono_ns=330647220881708
    sidecar anchor:     mono_ns=330647459112916
    filtered profile:   /tmp/hex-profile-runBareissDet-16.json.gz
    ```
- `leibniz-small-determinant`
  - Command: `scripts/profile/run_profile.sh ./.lake/build/bin/hexmatrix_bench Hex.MatrixBench.runLeibnizDet 8 5000000000`
  - Child row: `inner_repeats=128`, `per_call_nanos=24285055.343750`,
    `result_hash=0x6554`.
  - Leaf cost: Lean runtime and harness 57.5%, Lean own code 20.9%,
    allocation/free 17.4%, other system samples 4.2%, with no visible GMP
    leaf share on this small structured determinant. The largest leaves were
    refcount cold paths, `Hex.Matrix.inversionCount` folds, `mi_free`,
    `mi_malloc_small`, closure dispatch, list-to-array conversion, and
    permutation-list construction.
  - Inclusive ranking: `Hex.MatrixBench.runLeibnizDet` and its wrapper covered
    100.0% of retained samples, the Leibniz determinant fold covered 55.7%,
    `detTerm` covered 54.5%, `permutationVectors` construction covered 43.0%
    / 38.9% in the flat-map and map loops, `detSign` covered 29.9%, and
    `inversionCount` covered 15.3%. These costs are the expected factorial
    permutation/enumeration path measured by the registered
    `runLeibnizDet` target.
  - Diagnostics:
    ```text
    bench thread:       name='Thread <4895591>' tid=4895591
    regions:            2, total timed = 3132.9 ms
    expected samples:   ~3130 on bench thread
    retained samples:   3129 on bench thread (9 rejected outside windows)
    other-thread noise: 0 samples on non-bench threads within timed windows (informational)
    spawn anchor:       wall_ns=1780142627735394000, mono_ns=330661656259250
    sidecar anchor:     mono_ns=330661879149416
    filtered profile:   /tmp/hex-profile-runLeibnizDet-8.json.gz
    ```

The dominant inclusive costs all map to registered `HexMatrix.Bench` targets.
No unattributed dominant cost was observed.

## Concerns

- The FLINT `fmpz_mat.det` comparator pulls steadily ahead of
  `runBareissDet` across the entire ladder: raw ratio
  `0.973x → 0.062x` from `n = 128` to `n = 512`, and within the
  eligible range (`n = 320, 384, 512`) the adjusted ratio drifts from
  `0.057x` to `0.049x` — FLINT spends roughly 5% of Hex's wall time
  on the same surface, and the gap widens with `n`. This is an
  adverse trend at the `n³` determinant surface. The comparator is
  `informational`, so this is recorded for orientation rather than as
  a Phase-4 gate; the structural gap matches
  `SPEC/Libraries/hex-matrix.md §"External comparators"`'s rationale
  (FLINT uses multimodular reduction + CRT, structurally different
  from Hex's row-pivoted Bareiss fraction-free elimination over
  `Int`). A follow-up may file a narrow HO against
  `Hex.Matrix.bareiss` if a faster Hex determinant surface is wanted
  (for instance, a multimodular CRT path layered over the existing
  Bareiss kernel as a Tier-2 fast path).
