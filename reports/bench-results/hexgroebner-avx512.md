# Exact AVX-512 F4 row packets

Sixteen-lane canonical updates reduce the measured row-kernel times on this host. The two full-system campaigns do not establish an overall F4 speedup or the fastest-open-source milestone.

The native transition selects AVX-512 only after CPU and OS state checks. AVX2 and scalar fallbacks remain available. All packet validation precedes writes; a refused sixteen-lane packet falls back to eight-lane and scalar processing in order. Logical work, budgets, resumable state and complete non-time outputs agree.

## Retained kernel measurements

Host `chungus2` (AMD EPYC 9455); one algorithm thread, automatically leased CPU 11. Lean 4.35.0-rc3; Clang 23.1.3. Preparation is excluded; validation, allocation, elimination, decoding and full-output hashing are included. The registered cubic Cauchy families use fixed trial-major ladders and adjacent AB/BA comparisons, with a one-second batch target.

| Kernel | B/A geometric mean | Pair range | Below-signal flags |
|---|---:|---:|---:|
| u16-dense | 0.848907 | 0.762203–0.963825 | 0 |
| u16-strided | 0.930060 | 0.908454–0.960733 | 0 |
| m31-dense | 0.832561 | 0.755632–0.950957 | 0 |
| m31-strided | 0.936603 | 0.902001–0.971377 | 0 |

All 72 invocations, including 32 matched pairs and every complexity trial, are retained with equal complete-output hashes. No kernel repeat was needed.

## Full F4 candidate production

Both campaigns use the fixed seven-family, fourteen-input suite over 32003 and 2147483647, grevlex, degree scheduling, and one thread. Each campaign retains 56 processes in adjacent AB/BA order. The second is the single unchanged repeat after the first was inconclusive; the campaigns are reported separately. These are unchecked candidates. Certificate generation, independent native verification and kernel checking are excluded.

| Campaign | Process B/A | Candidate B/A | Process pair range | Peak RSS A/B (KiB) |
|---|---:|---:|---:|---:|
| f4 | 0.994089 | 0.991842 | 0.818400–1.184014 | 92464/92440 |
| f4-repeat | 0.992455 | 0.993317 | 0.839299–1.197078 | 92256/92440 |

All 112 completed processes (56 pairs) agree on complete bases and every non-time counter. There are no failures or timeouts. The small aggregate changes and broad pair ranges do not support an overall speed claim. Eight diagnostic cycle profiles retain fixed ABBA runs of Eco11 and Cyclic7, including raw perf data and outputs. They investigate the limited full-system effect, remain outside the timing ratios, and identify continuing row-scan work without establishing a language limitation.

## Verification and provenance

Clang and GCC each pass ASan/UBSan with AVX-512, forced AVX2, and scalar dispatch, with and without wide-integer reduction: twelve variants. The nine project gates include the executable/theory build, independent oracles, driver checks, benchmark verification, dependency/phase/manifest checks and source checks. Guarded standalone buffers cover all sixteen invalid lanes, source endpoints, strided/contiguous targets and narrow-gather refusal at the final cell. Instrumented full F4 tests require actual AVX-512 execution when supported. An untimed instrumented replay of all fourteen sweep inputs records 1128–22046092 sixteen-lane packets per input and agrees with every timed non-time output.

Baseline runtime `08e04a666b85`; timed prototype `1fcd281afc7f`; verified runtime `067f2508234c`, checks `a49e71708b6c`. The sole runtime-manifest difference after timing expands the standalone selftest; production sources are identical. The capsule includes exact source blobs, compiler commands, build logs, toolchain pins, raw samples, RSS, failures and verification logs. An initial generated harness exceeded Lean’s recursion-depth limit; that failed build is retained under diagnostics. The isolated coverage helper resolves it.

Capsule: `f4-avx512-067f2508234c.tar.xz`; SHA-256 `6bd4451a1705c715e46ab8990ee1b5346f29b80b8ae2cef80e16025f0fcd62c6`.

Regenerate with `python3 scripts/bench/groebner_avx512_report.py --archive reports/bench-results/raw/f4-avx512-067f2508234c.tar.xz --report reports/bench-results/hexgroebner-avx512.md --check`.
