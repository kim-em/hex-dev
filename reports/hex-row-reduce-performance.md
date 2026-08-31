# HexRowReduce Performance Report

## Bench targets

`bench/HexRowReduce/Bench.lean` gives every advertised executable operation a
direct mode-1 registration. Preparation is outside the timed region and result
forcing is inside it. The two declared input families are
`dense-rational-rref` and `rank-deficient-rational-nullspace`.

| Registration | Executable surface | Controlled family and schedule | Model |
| --- | --- | --- | --- |
| `runReduce` | `Matrix.rowReduce` | dense `I + J`, `n = 8, 12, 16, 24, 32, 48, 64` | `n³` |
| `runRank` | `Matrix.rowReduce_rank` | dense `I + J`, same ladder | `n³` |
| `runSpanCoeffs` | `Matrix.spanCoeffs` | dense `I + J`, same ladder | `n³` |
| `runSpanContains` | `Matrix.spanContains` | dense `I + J`, same ladder | `n³` |
| `runEchelonCoeffs` | `IsEchelonForm.echelonCoeffs` on prepared RREF | rank-deficient projection, `n = 128, 192, 256, 384, 512, 768` | `n` |
| `runEchelonSpanCoeffs` | `IsEchelonForm.spanCoeffs` on prepared RREF | dense `I + J`, `n = 16, 24, 32, 48, 64, 96, 128, 192` | `n²` |
| `runEchelonSpanContains` | `IsEchelonForm.spanContains` on prepared RREF | dense `I + J`, same ladder | `n²` |
| `runFreeCols` | `IsEchelonForm.freeCols` on prepared RREF | rank-deficient projection, `n = 64, 96, 128, 192, 256, 384, 512` | `n²` |
| `runNullspaceMatrix` | `Matrix.nullspaceBasisMatrix` | repeated half-size `I + J`, `n = 16, 24, 32, 48, 64` | `n³` |
| `runNullspace` | `Matrix.nullspace` | repeated half-size `I + J`, `n = 8, 12, 16, 24, 32, 48, 64` | `n³` |
| `runReducedMatrix` | `IsRowReduced.nullspaceMatrix` on prepared RREF | rank-deficient projection, `n = 128, 192, 256, 384, 512, 768, 1024` | `n³` |
| `runReducedNullspace` | `IsRowReduced.nullspace` on prepared RREF | rank-deficient projection, same ladder | `n³` |

All registrations use warm child-side repeats, a 1 s target batch, a 10 s
per-call cap, and `signalFloorMultiplier := 1.0`, which disables signal-floor
exclusion. The prepared vector ladders stop before their runtime
large-allocation transitions. Public wrappers and prepared span targets use
three outer trials, the cheap echelon helpers use five, and the allocation-heavy
prepared nullspace constructors use seven. The latter two explicitly use the
mode-1 slope tolerance `0.20`; all others use the default `0.15`.

## Verdicts

All twelve registrations returned `consistent_with_declared_complexity` in a
single clean suite run:

| Registration | `β` | `cMin`–`cMax` | Largest outer-trial spread |
| --- | ---: | ---: | ---: |
| `runReduce` | −0.007 | 802.820–837.334 | 10.3% |
| `runRank` | +0.012 | 759.887–834.390 | 15.3% |
| `runSpanCoeffs` | −0.037 | 833.125–904.413 | 5.9% |
| `runSpanContains` | −0.002 | 846.427–905.316 | 9.5% |
| `runEchelonCoeffs` | +0.079 | 135.255–152.256 | 19.0% |
| `runEchelonSpanCoeffs` | +0.041 | 812.217–910.210 | 20.2% |
| `runEchelonSpanContains` | +0.064 | 812.822–923.354 | 13.0% |
| `runFreeCols` | −0.034 | 8.536–9.386 | 11.8% |
| `runNullspaceMatrix` | — | 300.632–303.218 | 6.9% |
| `runNullspace` | −0.028 | 303.682–324.068 | 5.4% |
| `runReducedMatrix` | −0.166 | 0.391–0.532 | 30.4% |
| `runReducedNullspace` | −0.076 | 0.410–0.472 | 32.5% |

The largest spreads occur in allocation-heavy prepared constructors. Their
reported points are seven-trial medians; the table exposes the full observed
range rather than treating the fitted slopes as precise latency estimates.
`runNullspaceMatrix` has four verdict-eligible ratios after warmup trimming, so
mode 1 uses its bounded normalized constants without fitting a slope.

The machine-readable evidence is
`reports/bench-results/hex-row-reduce-phase4-scientific.json` (SHA-256
`440c703e3919d158b3cd93cb27484bda7b7efec97c1bd9c456ae44ac6d52257d`).
It records clean source commit
`f88a6ab24b235a474cf0d78ba416f69e77d0804e`, Lean 4.34.0-rc2,
lean-bench 0.1.0, the exact settings, every trial, result hashes, and host
metadata. It was produced in one process with:

```text
.lake/build/bin/hexrowreduce_bench run --filter Hex.RowReduceBench.run \
  --export-file reports/bench-results/hex-row-reduce-phase4-scientific.json
```

## Comparator ratios

None are declared. python-flint's public `fmpq_mat` route performs complete
rational-matrix JSON decoding and result encoding for every request; that
transport dominates the shared practical ladder, so a Hex/FLINT number would
not be a kernel ratio. The callable results also differ: Hex returns the full
row-operation transform, while python-flint RREF does not, and the
transform-dependent `spanCoeffs` witness has no canonical counterpart.

FLINT remains the independent correctness oracle through
`scripts/oracle/matrix_flint.py` and `hexrowreduce_emit_fixtures`; those checks
are conformance evidence, not timing evidence.

## Profile

Two deterministic `n = 64` cases were profiled from clean commit
`f88a6ab24b235a474cf0d78ba416f69e77d0804e` on an AMD EPYC 9455
(x86_64, 96 logical cores), NixOS 26.11 / Linux 6.12.100, with lean-bench
0.1.0 and samply 0.13.1 at 999 Hz. Raw profiles remain under `/tmp` and are
not committed.

For dense `runReduce`, 1,937 timed-thread samples were retained. Inclusive
time is 99.85% in `Matrix.rowReduce`, 99.79% in `rowReduceLoop`, and 98.40% in
the specialized `rowAdd` path. Leaf samples are 37.74% GMP arithmetic, 34.95%
allocation, 24.73% Lean runtime, 1.65% Lean/Hex own code, and 0.93% other.
Calibration residual was 0.963 ms against a 5 ms limit; off-thread samples
were zero and the ±5 ms sensitivity check passed.

For rank-deficient `runNullspaceMatrix`, 1,376 timed-thread samples were
retained. Inclusive time is 99.93% in `Matrix.nullspaceBasisMatrix`, 99.56% in
its single `Matrix.rowReduce` path, and 98.40% in `rowAdd`. Leaf samples are
38.01% GMP arithmetic, 36.26% allocation, 23.40% Lean runtime, 1.89% Lean/Hex
own code, and 0.44% other. Calibration residual was 0.480 ms; off-thread
samples were zero and sensitivity passed. Inspection of the generated C for
this registration also shows exactly one call to the specialized
`Matrix.rowReduce`, followed by nullspace construction and flat-array forcing.

Commands:

```text
LEAN_BENCH_SAMPLY_HOME=<lean-bench-samply> scripts/profile/run_profile.sh \
  .lake/build/bin/hexrowreduce_bench Hex.RowReduceBench.runReduce 64 3000000000
LEAN_BENCH_SAMPLY_HOME=<lean-bench-samply> scripts/profile/run_profile.sh \
  .lake/build/bin/hexrowreduce_bench Hex.RowReduceBench.runNullspaceMatrix 64 3000000000
```

## Concerns

None.
