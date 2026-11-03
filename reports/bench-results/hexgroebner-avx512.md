# Exact AVX-512 F4 row packets

Sixteen-lane updates are opt-in. The measured row kernels improve on this host; the full-system campaigns do not establish an overall F4 speedup or the fastest-open-source milestone.

Enable with `lake -R -KhexGroebnerAVX512=true build`; restore the default with `lake -R build`. CPU/OS checks additionally require AVX-512F/DQ/BW/VL and enabled YMM/ZMM state. AVX2 and scalar fallbacks remain available. Every packet validates before writing; refusal preserves the eight-lane/scalar failure prefix, work, budgets and resumable state. The optional dense-pivot cache retains its AVX2 path.

Host `chungus2` (AMD EPYC 9455 48-Core Processor); one algorithm thread, automatically leased CPUs recorded per campaign. Toolchain `leanprover/lean4:v4.35.0-rc3`. Native C: clang version 21.1.8; Lean-generated C: clang version 23.1.0 (https://github.com/llvm/llvm-project ea7d852a70e8bdfaf601d6626a760f9771b2c4b4). Sanitizer checks separately use Clang 23.1.3 and GCC 16.2.0. The original ELF compiler records also contain native Clang 21.1.8 and SDK Clang 23.1.0; the sanitizer compiler version must not be treated as the production compiler.

## Retained kernel measurements

Preparation is excluded; validation, allocation, elimination, decoding and complete-output hashing are included. The cubic Cauchy families use fixed trial-major ladders and adjacent AB/BA pairs, with one-second batches. Each source retains 72 invocations and 32 matched pairs, including all signal flags and every complexity trial. Exit code 2 is retained as a benchmark verdict, never treated as a successful operation by itself: every individual result must have status `ok`.

| Source / kernel | B/A mean | Pair range | Flags | n=64 | 128 | 256 | 512 |
|---|---:|---:|---:|---:|---:|---:|---:|
| Original source / u16-dense | 0.848907 | 0.762203–0.963825 | 0 | 0.948779 | 0.869458 | 0.794261 | 0.792616 |
| Original source / u16-strided | 0.930060 | 0.908454–0.960733 | 0 | 0.958940 | 0.935272 | 0.909504 | 0.917299 |
| Original source / m31-dense | 0.832561 | 0.755632–0.950957 | 0 | 0.948219 | 0.867532 | 0.770352 | 0.758196 |
| Original source / m31-strided | 0.936603 | 0.902001–0.971377 | 0 | 0.970445 | 0.942647 | 0.903818 | 0.930724 |
| Opt-in source / u16-dense | 0.839467 | 0.765258–0.943461 | 0 | 0.940709 | 0.867951 | 0.792060 | 0.767900 |
| Opt-in source / u16-strided | 0.931003 | 0.900949–0.964490 | 3 | 0.963878 | 0.938187 | 0.904121 | 0.918894 |
| Opt-in source / m31-dense | 0.832084 | 0.764637–0.942522 | 0 | 0.933945 | 0.861053 | 0.777665 | 0.766525 |
| Opt-in source / m31-strided | 0.934346 | 0.899599–0.972174 | 0 | 0.969375 | 0.941600 | 0.903488 | 0.924167 |

All complete-output hashes agree. The original source used automatic sixteen-lane dispatch; the revised source uses the explicit build option. No timings are pooled across sources or campaigns. The 3 matched samples carrying below-signal flags remain in the ratios; those observations have that limitation. Performance on other microarchitectures, one-byte coefficients and generic four-byte Montgomery kernels remains unevaluated.

## Full F4 candidate production

Each campaign uses the fixed seven-family, fourteen-input suite over 32003 and 2147483647, grevlex, degree scheduling, and one thread. Each source has one first campaign and exactly one unchanged repeat after an inconclusive result, retaining all 56 processes per campaign in adjacent AB/BA order. These are unchecked candidates; certificate generation, independent native verification and kernel checking are excluded from timing.

| Source / campaign | Process B/A | Candidate B/A | Process pair range | Peak RSS A/B (KiB) |
|---|---:|---:|---:|---:|
| Original source / f4 | 0.994089 | 0.991842 | 0.818400–1.184014 | 92464/92440 |
| Original source / f4-repeat | 0.992455 | 0.993317 | 0.839299–1.197078 | 92256/92440 |
| Opt-in source / f4 | 0.994332 | 0.989836 | 0.849887–1.291619 | 92208/92348 |
| Opt-in source / f4-repeat | 1.002712 | 0.991370 | 0.887258–1.287754 | 92208/92316 |

All 224 completed processes (112 pairs) agree on complete bases and every non-time counter, with no failures or timeouts. The small aggregate changes and broad pair ranges do not establish an overall speed claim. The revised default executables, including the benchmark executable, are byte-for-byte identical to the original baseline. The original capsule also retains eight fixed ABBA diagnostic cycle profiles of Eco11 and Cyclic7; these remain outside timing ratios and do not establish a language limitation.

## Verification and provenance

Clang and GCC each pass ASan/UBSan for opt-in AVX-512, forced AVX2 and scalar dispatch, with and without wide-integer reduction: twelve variants. The nine project gates cover the executable/theory build, independent oracles, drivers, benchmark verification, dependency/phase/manifest checks and source checks. The expanded standalone test exhausts one-byte arithmetic and checks deterministic factors, random odd moduli, all sixteen invalid lanes, exact gather-padding boundaries, out-of-range columns, cross-packet ordering and mode admission. Six deliberately broken guards each fail that test. The compiled harness checks all six sixteen-lane width/layout paths and full F4 execution. `HEX_GROEBNER_REQUIRE_AVX512=1` requires hardware coverage in manual runs; hosted CI does not promise that ISA.

Original source: baseline `08e04a666b85`, candidate `1fcd281afc7f`; instrumented sweep replays record 1128–22046092 sixteen-lane packets per input and equal non-time output.

Opt-in source: baseline `13a33eb6a851`, candidate `13a33eb6a851`; instrumented sweep replays record 1128–22046092 sixteen-lane packets per input and equal non-time output.

Verified runtime `13a33eb6a851`, checks `7abfc10437ea`. The revised packet-count driver is generated by committed code and replayed under both compilers. Both the production object and retained probe objects track the new header; an unchanged probe is cached, a header edit rebuilds it, and restoring the header rebuilds the identical original object. Capsules include exact source blobs, native build options, external compiler inputs, raw samples, RSS and verification logs. The original capsule retains the failed recursion-depth build under diagnostics; its test driver was split into a smaller helper.

Original capsule: `f4-avx512-067f2508234c.tar.xz`, SHA-256 `6bd4451a1705c715e46ab8990ee1b5346f29b80b8ae2cef80e16025f0fcd62c6`.
Revised capsule: `f4-avx512-optin-13a33eb6a851.tar.xz`, SHA-256 `a1c5b0c694934e6a9d36c36b8184abc1e3e27929db7f6a3d1aebd2bda0280ba5`.

Regenerate with `python3 scripts/bench/groebner_avx512_report.py --archive reports/bench-results/raw/f4-avx512-067f2508234c.tar.xz --review reports/bench-results/raw/f4-avx512-optin-13a33eb6a851.tar.xz --report reports/bench-results/hexgroebner-avx512.md --check --current`.
