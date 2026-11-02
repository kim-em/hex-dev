# Bounded native zeroing for wide matrix continuations

The public native continuation now uses the existing bounded zero-buffer
provider when its Lean workspace phase executes. Scalar continuation still
uses the independent byte-at-a-time implementation. Both address/allowance
checks and charge order are unchanged; each native buffer call admits at most
one MiB. Larger buffer sizes fall back to the existing portable implementation.
The production F4 shape guard remains unchanged, so this is an improvement
to the public continuation API rather than a production F4 speedup.

Source fingerprint `a3938be198b4` is frozen at snapshot
`7774abf03654040b3495f5b18e440f28adf89a1e`; compute SHA-256 is
`1e06b44e72a1a09211968337760c6131eaa7ff9688aa952b276f96feebd8f37e`. The build uses Lean 4.35.0-rc3 with
archived compiler/link flags and a fresh detached worktree sharing only pinned
dependency packages. The native row/zero provider code is unchanged.

`step_spec` proves exact equality of native and scalar phase models through
`Matrix.zerosWith_spec`. Scheduling/resumption and workspace-transition proofs
use this equality explicitly. Full `finish_reference` and production-dispatch
proofs, ordinary-import replay and standard axiom guards pass. No proof depends
on an additional axiom. Agreement with native C remains a tested obligation.

The [earlier dispatch measurements](hexgroebner-continuation-dispatch.md) found
about a fourfold unrestricted-continuation regression above 65,536 columns.
A diagnostic user-cycle profile of both complete registered sweeps on one
automatically leased CPU found no lost samples. About 29.7% of continuation
samples land in `lean_byte_array_push` and 15.2% in the `Matrix.zeros` loop;
the reference spends about 1.3% in native memset. These whole-process profiles
include setup, initialization and all widths; they are cost attribution, not
per-width timing comparisons. Raw perf captures, reports and benchmark exports
are retained separately from scientific timing campaigns.

The fixed wide sparse kernels use prime 65537, eight reducers and eight targets,
with a pivot at the final column. Preparation is excluded. Validation, workspace
initialization, complete elimination and decoded rows/metadata/all eight
counters are included and hashed. Work is linear in columns for these fixed
row counts. Each experiment alternates adjacent whole sweeps AB then BA,
requesting one thread on an automatically leased CPU of shared host chungus2.
All completed samples, repeat counts, floor flags, RSS and load context remain
visible; there is no host filtering or unchanged repeat.

The before/after campaign compares `matrixWide` in the guarded dispatch source
`95c9b375e69d` with `matrixWide` in this source. A separate campaign compares
`matrixWideReference` and `matrixWide` in the same new executable. Full hashes
agree at every width in both blocks of each campaign.

| Block | Columns | Old continuation ms | Native-zero continuation ms | New/old | New/reference in separate campaign |
| --- | ---: | ---: | ---: | ---: | ---: |
| 0 | 65536 | 0.2962 | 0.3084 | 1.0411 | 1.0720 |
| 0 | 65537 | 1.0593 | 0.3106 | 0.2932 | 1.1159 |
| 0 | 131072 | 2.1170 | 0.6616 | 0.3125 | 1.2336 |
| 0 | 262144 | 4.2364 | 1.3021 | 0.3074 | 1.2201 |
| 1 | 65536 | 0.3096 | 0.2960 | 0.9561 | 1.1209 |
| 1 | 65537 | 1.0564 | 0.3109 | 0.2943 | 1.1024 |
| 1 | 131072 | 2.1973 | 0.6653 | 0.3028 | 1.2131 |
| 1 | 262144 | 4.1839 | 1.2958 | 0.3097 | 1.1606 |

Above 65,536 columns the continuation takes roughly 29–31% of its former time,
but remains about 10–23% slower than the reference in the separate observation.
The measured range ends at 262,144 columns, where each four-byte buffer is
exactly one MiB. The reported gain does not cover larger buffers. At 65,536
columns the native workspace phase already performs direct zeroing,
so this change does not replace that work. These finite kernel measurements
do not establish an asymptotic model or a full-system speedup.
Paired signal-floor flags: 0 of 16 pairs; all samples are retained.

The [14-input medium development suite](hexgroebner-medium.md) separately
compares the new candidate driver with shipping dispatch source `0a7fa663e970`.
Every one of 28 pairs has equal complete JSON fields except candidate time,
including every reduced-basis coefficient/exponent and every statistic.
All 56 processes complete, with no failures or timeouts. The suite remains
within the native scheduler geometry, where production dispatch is unchanged.
Identical GNU-time wrappers, one requested thread, adjacent AB/BA, 60-second,
16-GiB and 64-MiB output limits and all startup/output are included. Certificate
generation, independent certification and kernel checking are excluded.

The process family-balanced geometric mean is 0.9893, median 0.9919, range 0.7723–1.3288; CPU 73, peak RSS baseline/new 124052/124188 KiB. Internal candidate geometric mean is 1.0028, range 0.8568–1.1321. Production does not reach the changed phase on this suite. This is a null
comparison of the changed path, rather than evidence for its effect on F4;
the observed process/candidate spread measures unrelated variation. No further
no-work control is required or collected.

Two other source-specific experiments are retained and restored. Symbolic
support loops using `HashSet.containsThenInsert` (`342b8877ccca`) have complete
output/counter equality on 28 pairs, candidate ratio 0.9966 and process ratio
0.9763; the result is inconclusive. Hoisting matrix-order projections
(`03eb28702ea8`) preserves complete hashes in four-width before/after and
reference campaigns, with no clear improvement. Its individual outliers,
complexity verdicts and raw exports remain visible. Neither source is part of
this implementation, and none of these campaigns is pooled.

All executable/theory/conformance builds, independent matrix/division/basis
oracles, both 1,134-case drivers, eight Clang/GCC sanitizer/SIMD/scalar/remainder
configurations, complete kernel replay/axiom guards, bench verification and
DAG/phase/release/header/line checks pass. Existing large conformance covers
65,535/65,536/65,537-column frames at every coefficient width, exact counters,
paused states, malformed inputs, exhaustion and saved-buffer ownership.
Additional compiled checks compare the exact workspace-phase buffers and
counters of `advanceKernels` and `advancePortable` at 65,537 and 262,145
columns, including the native-zero fallback boundary. Prepared saved buffers
remain empty.
Sanitizer leak detection is disabled under mimalloc; explicit saved-snapshot
checks supplement it.

The production guard remains appropriate while the continuation is slower than
the reference above it. Larger buffers beyond one MiB, actual many-row wide
F4 systems, the row-count limit, probabilistic/parallel elimination and remaining
SPEC correctness/field/performance milestones still require work. The measured byte-by-byte zeroing cost is removed for buffers up to one MiB;
larger buffers retain that implementation.

[Raw capsule f4-workspace-zero-a3938be198b4](raw/f4-workspace-zero-a3938be198b4.tar.gz): SHA-256 `8bdb317815f7bbda719e80e509bced0a5924bacfd01b7bec289448975cac80fb`, 479 payloads, each read back and digest checked.

[Raw capsule f4-symbolic-hash-342b8877ccca](raw/f4-symbolic-hash-342b8877ccca.tar.gz): SHA-256 `46138b727fd822e5e8deee0450d9fdee936220b478f11ba4aad7bdca6b346d61`, 396 payloads, each read back and digest checked.

[Raw capsule f4-workspace-order-03eb28702ea8](raw/f4-workspace-order-03eb28702ea8.tar.gz): SHA-256 `c7e23ac19157836751789a3188be6a618e66f2c022bb645f044368c7992c4949`, 221 payloads, each read back and digest checked.

[Supplementary source, native-boundary and loader audit](raw/f4-followup-audit-a3938be198b4.tar.gz): SHA-256 `de837be4725c97920a96d8d308823b66700e8eef3357c782d3a51892a9f30c5a`, 50 payloads, read back and digest checked. This includes the added workspace-boundary checks and eight final native configurations, post-capture GamBa medians/totals, both help outputs and actual loaded-file/priority/thread audit. Timed raw outputs and the original capture scripts remain unchanged in the original capsules.
