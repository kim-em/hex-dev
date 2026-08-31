# HexRowReduce Performance Report

## Bench targets

All compiled performance targets use mode 1, the strongest ordered evidence
mode. The formulas below are copied from the `setup_benchmark` registrations
in `bench/HexRowReduce/Bench.lean`.

| Registration | Executable surface | Family and schedule | Declared complexity |
| --- | --- | --- | --- |
| `Hex.RowReduceBench.runReduce` | `Matrix.rowReduce` | dense `I + J`, `n = 8, 12, 16, 24, 32, 48, 64` | `n ^ 3` |
| `Hex.RowReduceBench.runRank` | `Matrix.rowReduce_rank` | dense `I + J`, same ladder | `n ^ 3` |
| `Hex.RowReduceBench.runSpanCoeffs` | `Matrix.spanCoeffs` | dense `I + J`, same ladder | `n ^ 3` |
| `Hex.RowReduceBench.runSpanContains` | `Matrix.spanContains` | dense `I + J`, same ladder | `n ^ 3` |
| `Hex.RowReduceBench.runEchelonCoeffs` | `IsEchelonForm.spanCoeffs` on prepared RREF | dense `I + J`, `n = 16, 24, 32, 48, 64, 96, 128, 192` | `n ^ 2` |
| `Hex.RowReduceBench.runEchelonContains` | `IsEchelonForm.spanContains` on prepared RREF | dense `I + J`, same ladder | `n ^ 2` |
| `Hex.RowReduceBench.runNullspaceMatrix` | `Matrix.nullspaceBasisMatrix` | repeated half-size `I + J`, `n = 16, 24, 32, 48, 64` | `n ^ 3` |
| `Hex.RowReduceBench.runNullspace` | `Matrix.nullspace` | repeated half-size `I + J`, `n = 8, 12, 16, 24, 32, 48, 64` | `n ^ 3` |
| `Hex.RowReduceBench.runReducedMatrix` | `IsRowReduced.nullspaceMatrix` on prepared RREF | rank-`n / 2` projection, `n = 128, 192, 256, 384, 512, 768, 1024` | `n ^ 3` |
| `Hex.RowReduceBench.runReducedNullspace` | `IsRowReduced.nullspace` on prepared RREF | rank-`n / 2` projection, same ladder | `n ^ 3` |

All targets use warm child-side repeats, a 10 s call cap, and
`signalFloorMultiplier := 1.0`; this records the high-startup-floor host
condition without changing the model, ladder, or cap. The first eight use
three outer trials. The two large prepared-nullspace targets use seven outer
trials so scheduler stalls do not control the median.

## Verdicts

Mode 1 applies directly to every target, so no weaker mode is needed. Every
registration returned `consistent_with_declared_complexity` at its committed
scientific settings:

| Registration | Verdict | `β` | `cMin`–`cMax` |
| --- | --- | ---: | ---: |
| `runReduce` | consistent with declared complexity | +0.032 | 789.267–848.248 |
| `runRank` | consistent with declared complexity | +0.010 | 808.193–862.869 |
| `runSpanCoeffs` | consistent with declared complexity | −0.042 | 855.621–918.002 |
| `runSpanContains` | consistent with declared complexity | −0.015 | 829.454–880.156 |
| `runEchelonCoeffs` | consistent with declared complexity | +0.045 | 853.973–987.736 |
| `runEchelonContains` | consistent with declared complexity | +0.052 | 545.413–728.468 |
| `runNullspaceMatrix` | consistent with declared complexity | — | 342.639–375.448 |
| `runNullspace` | consistent with declared complexity | −0.049 | 180.790–199.600 |
| `runReducedMatrix` | consistent with declared complexity | +0.076 | 0.392–0.926 |
| `runReducedNullspace` | consistent with declared complexity | +0.000 | 0.251–0.333 |

`runNullspaceMatrix` has four verdict-eligible ratios after the declared
warmup trim, so the harness returns the consistent verdict from the bounded
normalized constants without a fitted slope.

The machine-readable evidence is
`reports/bench-results/hex-row-reduce-phase4-scientific.json` (SHA-256
`78a610bc2eca63cbb4f1aa120d40cd869f58b610891f69d2b4e49fd8a3059061`).
Each row records clean source commit
`27287f7bd4468a407d2d86424b54cfc0820e7826`, Lean 4.34.0-rc2,
lean-bench 0.1.0, and its exact registration settings. To isolate the host's
cross-target frequency changes, each case was collected in a fresh process:

```text
.lake/build/bin/hexrowreduce_bench run <registration> \
  --export-file /tmp/<registration>.json
```

The ten one-result exports were combined without modifying their result rows.
The 29 fixed registrations are exact-hash comparator/protocol anchors, not
performance claims. Every observed hash matched its declared expected hash;
their medians and hashes are reported below.

## Comparator ratios

The named informational comparator is **python-flint fmpq_mat RREF**:
python-flint 0.9.0 backed by FLINT 3.6.0 `fmpq_mat.rref`. It receives the
same canonical rational JSON matrices through the persistent driver.
Hex/FLINT result hashes agree at every rung.
The protocol-only overhead anchor is 12.310 µs per call, with expected hash
`0x84d361908b60d650`.

RREF and rank (`Hex / FLINT`):

| `n` | Hex median | FLINT median | Hash | Raw ratio | Overhead-adjusted ratio |
| ---: | ---: | ---: | --- | ---: | ---: |
| 8 | 303.192 µs | 136.072 µs | `0x6ca6178de0126e10` | 2.23× | 2.45× |
| 12 | 1.337 ms | 277.446 µs | `0x3548b1dee30b7444` | 4.82× | — |
| 16 | 3.216 ms | 477.460 µs | `0xd6434cb7f79aa670` | 6.73× | — |
| 24 | 10.122 ms | 1.056 ms | `0xab53897f9681f1ce` | 9.58× | — |
| 32 | 23.041 ms | 1.928 ms | `0x69bb3c6679a2cc4b` | 11.95× | — |
| 48 | 79.741 ms | 4.461 ms | `0xa23e2013cacf6e4e` | 17.88× | — |
| 64 | 155.830 ms | 7.252 ms | `0x91317157ea95e9af` | 21.49× | — |

Canonical free-variable nullspace basis (`Hex / FLINT`):

| `n` | Hex median | FLINT median | Hash | Raw ratio | Overhead-adjusted ratio |
| ---: | ---: | ---: | --- | ---: | ---: |
| 8 | 108.201 µs | 107.273 µs | `0xd2e37217fbfa8544` | 1.01× | 1.14× |
| 12 | 346.639 µs | 208.288 µs | `0x35220a3c9f4587fe` | 1.66× | 1.77× |
| 16 | 984.418 µs | 445.893 µs | `0x0003b3f1256cc8a8` | 2.21× | — |
| 24 | 4.003 ms | 803.995 µs | `0xd57d96c775400424` | 4.98× | — |
| 32 | 9.177 ms | 1.343 ms | `0xe59fa635b61f86d7` | 6.84× | — |
| 48 | 29.139 ms | 3.386 ms | `0x5c4539422fa584e4` | 8.61× | — |
| 64 | 65.161 ms | 6.548 ms | `0x60ac962101f19bc3` | 9.95× | — |

All rungs are eligible: comparator overhead is below 50% of comparator time
and all calls are below the 1 s soft ceiling. Adjusted ratios are shown where
overhead exceeds 5% of comparator time. Both curves climb over the measured
range (RREF 2.23×→21.49×; nullspace 1.01×→9.95×). This is expected for the
informational comparison: Hex's RREF returns and forces the full row-operation
transform, whereas python-flint exposes only RREF and rank; the nullspace
anchor derives its basis from that tuned FLINT RREF. The trend therefore does
not contradict a gating goal or the declared comparator rationale.
`spanCoeffs` is classified
`no-comparable-surface-in-named-comparator` because its witness depends on the
chosen transform.

The source artifact is
`reports/bench-results/hex-row-reduce-phase4-comparators.json` (SHA-256
`9b25b0172ccc0ba283c96c9e8b0776a6a0766b912cbf4a33909fc559a6ca12bb`),
recorded from the same clean commit with:

```text
HEX_FLINT_BENCH_PYTHON=<python-flint-0.9.0-venv>/bin/python \
  .lake/build/bin/hexrowreduce_bench run <all 29 fixed anchors> \
  --export-file reports/bench-results/hex-row-reduce-phase4-comparators.json
```

## Profile

Both deterministic cases were profiled on clean commit
`27287f7bd4468a407d2d86424b54cfc0820e7826` on an AMD EPYC 9455
(x86_64, 96 logical cores), NixOS 26.11 / Linux 6.12.100, using lean-bench
0.1.0 and samply 0.13.1 at 999 Hz. Raw Firefox profiles remain in `/tmp` and
are not committed, as required by the profiling contract.

**`dense-rational-rref`, `runReduce`, `n = 64`.** Command:

```text
LEAN_BENCH_SAMPLY_HOME=<lean-bench-samply> scripts/profile/run_profile.sh \
  .lake/build/bin/hexrowreduce_bench Hex.RowReduceBench.runReduce 64 3000000000
```

Leaf self-time is 45.90% GMP big-integer arithmetic, 35.25% allocation/free,
13.79% Lean runtime, 3.88% `HexRowReduce` own code, and 1.18% other native
code (2037 retained samples). The leading leaf functions are `free` (14.97%),
`malloc` (13.99%), `gmpz_add` (12.47%), `gmpz_init_set_ui` (7.31%), and
`Rat.mul` (4.66%). Inclusive `Matrix.rowReduce` is 99.90%,
`rowReduceLoop` 99.85%, `eliminateColumn` 98.72%, and the specialized
`rowAdd` loop 98.48%. This is the expected Gauss--Jordan hot path; exact
rational updates explain the GMP and allocation-heavy leaf budget.

Diagnostics: absolute-monotonic calibration residual 0.909 ms (5 ms limit),
2040.3 ms total timed region, 2037 retained bench-thread samples, zero
off-thread samples in the windows, ±5 ms sensitivity passed, confidence
passed. Local profile: `/tmp/hex-profile-runReduce-64.json.gz`.

**`rank-deficient-rational-nullspace`, `runNullspace`, `n = 64`.** Command:

```text
LEAN_BENCH_SAMPLY_HOME=<lean-bench-samply> scripts/profile/run_profile.sh \
  .lake/build/bin/hexrowreduce_bench Hex.RowReduceBench.runNullspace 64 3000000000
```

Leaf self-time is 47.29% GMP big-integer arithmetic, 33.44% allocation/free,
14.58% Lean runtime, 3.93% `HexRowReduce` own code, and 0.76% other native
code (2751 retained samples). The leading leaf functions are `free` (15.34%),
`gmpz_add` (14.76%), `malloc` (11.74%), `gmpz_init_set_ui` (8.80%), and
`realloc` (5.49%). Inclusive `Matrix.rowReduce` is 99.67%,
`rowReduceLoop` 99.64%, `eliminateColumn` 98.22%, and the specialized
`rowAdd` loop 98.07%. The nullspace wrapper is inclusive of that RREF work;
the subsequent `IsRowReduced.nullspace` construction is only 0.25% and
`pivotIndexAux` 0.15% here. The registered public-wrapper benchmark therefore
attributes the dominant cost to the same cubic elimination phase named by the
SPEC, while the prepared registrations separately cover the constructor.

Diagnostics: absolute-monotonic calibration residual 0.768 ms (5 ms limit),
2763.5 ms total timed region, 2751 retained bench-thread samples, zero
off-thread samples in the windows, ±5 ms sensitivity passed, confidence
passed. Local profile: `/tmp/hex-profile-runNullspace-64.json.gz`.

## Concerns

None.
