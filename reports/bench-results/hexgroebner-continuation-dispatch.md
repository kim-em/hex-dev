# Proved finite-field F4 matrix continuation dispatch

Production uses bounded native continuations after the small bulk frame declines,
provided there are at most 65,536 columns and total input rows. Larger matrices
retain the reference route with bounded native scan/gather kernels. The shape
guard avoids a measured roughly fourfold regression in Lean-scheduled continuation
completion above the native frame's column cap. The unrestricted continuation
remains available and measured for further optimization.

`MatrixState.finish_reference` proves exact equality with `Elimination.reference`
for every input, budget, quantum and provider, including errors and all eight
matrix counters. `Elimination.run_spec`, from
`HexGroebner.EliminationDispatchProof`, connects that equality to production dispatch.
Public-import replay and axiom guards use only `propext`, `Classical.choice`
and `Quot.sound`. The executable import graph excludes the optional proof stack.
Agreement between native C and the Lean model is tested.

The measured guarded source fingerprint is `95c9b375e69d`. The shipping source
fingerprint is `0a7fa663e970`; fresh builds produce exactly the same SHA-256 for
both compute executables. The retained runtime-identity audit connects these
source variants without another unchanged timing run. All measurements are single-thread
observations on shared host chungus2 (EPYC 9455, AVX2). Automatically leased CPUs,
load context, exact commands, inputs, outputs, failures and RSS are retained.
No host-activity filtering or quiet-core wait is used. Each campaign has adjacent
AB then BA arms; kernel arms alternate whole sweeps. Source snapshots are fresh
detached worktrees sharing only pinned dependency packages. Lean is 4.35.0-rc3;
the recorded SDK Clang wrapper and link flags are archived. Runtime patches and
source blobs permit reconstruction from main commit
`1420b84ce3aa2e48781f11244dc51a5b504c090b`.

| Source fingerprint | Frozen snapshot | Compute SHA-256 |
| --- | --- | --- |
| `9ddab5fe4bf1` | `ff6dd26c6339f105f39a0a2a1f20c8dd1f18ddbb` | `59ec7eb7e26cecdd7e1ff43b878b1cb008f82890aeefed34cbc650888dd8368b` |
| `a0a3d303d957` | `788bd4b645aec72d71785da3fa1d45536d58350b` | `e951f434fae01f75eea53b7bca225d2322439e1543a9b19dcec96b62976ac253` |
| `95c9b375e69d` | `f067040d9e97f065cb9515d5a0b12d43f85cfa0c` | `e913bc8129e2027e18056f4bfb9afb56d26cbfa3b7ca01005b9d384b0f6b5d50` |
| `0a7fa663e970` | `8d83b29c3ef99062f4816ba6217117412f88f802` | `e913bc8129e2027e18056f4bfb9afb56d26cbfa3b7ca01005b9d384b0f6b5d50` |

The 14-input grevlex development corpus contains cyclic7, Katsura8, Eco11,
Noon5, Reimer6, MinRank and dense quadratic6, each over primes 32003 and
2147483647. It is the [existing medium corpus](hexgroebner-medium.md), with no
held-out or acceptance claim. The before/after baseline has source fingerprint
`dd2370a9e993`, whose measured tree equals main commit `1420b84ce3`; its
[source-pinned report](hexgroebner-msolve-dd2370a9e993.md) retains full provenance.
All final before/after JSON fields except `candidateNanos` agree exactly,
including complete reduced bases, metadata and every F4 statistic.

Whole-process time includes startup, parsing, candidate production, final
interreduction and complete reduced-basis output under identical GNU-time
wrappers. Each process has a 60-second, 16-GiB address-space and 64-MiB output
limit. Each final campaign completes 56 processes and 28 complete-basis
comparisons with zero failures or timeouts. Certificate generation, independent
native certification and kernel checking are separate and excluded.

The source-pinned msolve checkout is clean at
`3672113ee2c696a2ac9c637636e0f7214f500ba1`, compiled with Clang 23.1.3,
`-O3 -march=native` resolving to znver5. GMP 6.3.0, MPFR 4.2.2 and FLINT 3.6.0
linkage and the direct ELF's recorded native compiler command are archived.
Both engines request one algorithm thread. Exact mode 2 and probabilistic mode
42 are separate campaigns; seeds and probabilistic diagnostics are retained.
Hex internal candidate timings are never compared with msolve process timings.

| Final process ratio | Equal-family geometric mean | Median | Range | CPU | Peak RSS A/B KiB |
| --- | ---: | ---: | --- | ---: | ---: |
| Selected/baseline | 0.9957 | 0.9864 | 0.8165–1.2968 | 33 | 126776/125020 |
| Hex/msolve exact 2 | 1.8922 | 2.0065 | 0.6647–3.1588 | 30 | 124956/20292 |
| Hex/msolve probabilistic 42 | 2.0627 | 2.0126 | 0.6905–4.8613 | 75 | 124336/20292 |

Memory A/B follows the archived arms: before/after A is baseline and B is selected;
for comparators A is Hex and B is msolve. The paired internal candidate-time
geometric mean is 0.9864, with ratio range 0.9614–1.0359. These internal durations
are separate from process wall time.

The equal-family mean first combines paired observations geometrically within
each family, then weights the seven families equally. The final before/after
process difference is inconclusive. Individual ratios and all completed samples
remain visible. These observations establish neither fastest-open-source
leadership nor a compiler/runtime impossibility.

| Family | Selected/baseline | Hex/msolve exact 2 | Hex/msolve probabilistic 42 |
| --- | ---: | ---: | ---: |
| cyclic | 0.9866 | 3.0889 | 3.7101 |
| kat | 0.9726 | 2.4226 | 2.3083 |
| eco | 0.9853 | 1.9138 | 3.0198 |
| noon | 0.9841 | 1.8544 | 1.7500 |
| reimer | 0.9835 | 2.3937 | 2.7119 |
| minrank | 0.9923 | 0.9451 | 0.9538 |
| dense-quadratic | 1.0688 | 1.4457 | 1.3573 |

Supplementary source-specific campaigns are retained separately and never pooled.
The initial selected source `9ddab5fe4bf1` has before/after process ratios
1.0010 and 0.9964 (one allowed unchanged repeat after the inconclusive first
campaign); its internal candidate ratios are 0.9905 and 0.9782. Its matched
msolve ratios are 1.8655 and 2.1018. Source `a0a3d303d957`, with proof imports
separated and stronger tests but unrestricted continuation dispatch, has process
ratios 0.9960, 1.8417 and 2.0210 against baseline, exact msolve and probabilistic
msolve respectively. Every campaign completes all 28 basis comparisons and
retains all 56 processes without failures. Changed sources have distinct
snapshots and manifests. The final source has one campaign per comparison and
no unchanged repeat.

There is no full-system before/after evidence above either native shape limit,
and the row-count boundary is not measured here. The wide fixture uses only
eight reducers and targets. Hard F4 matrices with many rows remain acceptance
work.

The registered `matrixWideReference`, `matrixWide` and `matrixWideSelected`
kernels hold the field (65537), eight reducers and eight targets fixed while
varying the column count. Sparse tails force scanning to the final column.
Preparation is excluded; validation, allocation, elimination, complete decoded
rows/metadata and every matrix counter are included. Full hashes agree across
all arms at every width. Linear work follows from a fixed number of scans plus
workspace initialization and column ordering.

| Block | Columns | Unrestricted/reference at a0a3d303d957 | Selected/reference at 95c9b375e69d |
| --- | ---: | ---: | ---: |
| 0 | 65536 | 1.1196 | 0.8123 |
| 0 | 65537 | 4.1807 | 0.6919 |
| 0 | 131072 | 4.3702 | 0.6451 |
| 0 | 262144 | 4.1653 | 0.5715 |
| 1 | 65536 | 0.8577 | 1.1041 |
| 1 | 65537 | 3.9655 | 1.0533 |
| 1 | 131072 | 3.9239 | 1.1138 |
| 1 | 262144 | 3.9616 | 1.0396 |

The two columns above are separate experiments on distinct frozen executables,
not a pooled before/after claim. The unrestricted continuation's approximately
4× cost above 65,536 columns motivates the production guard. Raw exports retain
all repeats, durations, RSS, result hashes, signal-floor flags and complexity
verdicts. These finite observations do not establish an asymptotic model.
Kernel paired signal-floor flags: 0 of 16 pairs; all are retained.

Four diagnostic user-cycle profiles of cyclic7 at the two prime widths explain
why matrix-frame selection has limited full-system effect. Each arm completes
with identical output and counters; all profiles report zero lost samples.
Native SIMD scan arithmetic accounts for about 20–21% of sampled cycles, batched
monomial products for about 7–9%, and allocation, reference counting and monomial
preparation remain visible. This is sampled cost attribution including startup,
not timing or acceptance evidence. These costs remain optimization targets;
the profiles do not establish an unavoidable Lean limitation.

Final validation builds the executable and theory libraries, all conformance
modules, both drivers and benches. Independent oracles cover 175 exact modular
matrices, 1,288 divisions and 567 reduced bases (1,134 strategy profiles). Reduced
bases are compared with SymPy and Singular. Each driver checks all 1,134 complete outputs/counters
plus malformed inputs and resource boundaries. Eight Clang/GCC native
configurations include ASan/UBSan and scalar/SIMD/remainder variants. An isolated
65-input F4 computation exceeds the bulk target cap, completes a successful
native continuation, and agrees in complete candidate metadata, output and
statistics with both native providers disabled. Its instrumented window verifies the bulk decline,
successful terminal continuation, positive reductions, zero rows, a non-unit
inverse, the configured phase-loop cap and zero admissions to
standalone matrix primitives. The loop counter does not measure actual machine
instructions, elapsed time or allocation volume inside each phase. Larger
production shapes may legitimately use those reference primitives. Native tests
cover saved snapshots and malformed prefixes. Benchmark verification, 14 DAG regression tests and DAG/phase/release/
header/line checks pass. Sanitizer leak detection is disabled under mimalloc;
ownership and saved-snapshot checks supplement it.

The SPEC's remaining performance acceptance requires the hard and held-out
families, wider field/extension coverage, parallel sweeps, solved coverage,
matched current open-source contenders and separate certification/native-
verification/kernel-checking costs. The issue remains open.

[Raw capsule f4-continuation-9ddab5fe4bf1](raw/f4-continuation-9ddab5fe4bf1.tar.gz): SHA-256 `4dbdc0873aa626a0dd25ba4aec981841d6ba20ff2c74e29bd0c80965635b45f3`, 1060 payloads. Every payload was read back and its digest checked.

[Raw capsule f4-continuation-a0a3d303d957](raw/f4-continuation-a0a3d303d957.tar.gz): SHA-256 `0075e9e99b165c5ff3dd23d877227d6fd4ce0f3a3148e2944b0e1665c50c8912`, 940 payloads. Every payload was read back and its digest checked.

[Raw capsule f4-continuation-dispatch-0a7fa663e970](raw/f4-continuation-dispatch-0a7fa663e970.tar.gz): SHA-256 `e4fabe508e8adbe3fc0067895430a5bfd56ec8f093c8f971bfbf8c81a0a95c4d`, 1110 payloads. Every payload was read back and its digest checked.
