# Symbolic support queues

Support batching preserves the first-occurrence queue order and the complete reduced basis. A dynamically growing arena bitmap replaces support hash lookup; a bounded native operation validates at most 4096 u32 IDs before updating the bitmap and pending queue. The portable definition has the same result, rejection and ownership contract. Bitmap initialization and growth add equal explicit work and packed-byte charges. The pending queue still uses Lean’s array of natural numbers; this change does not establish fully packed F4 scheduling storage.

These are shared-host development measurements, not a fastest-open-source milestone. Candidate production excludes certificate generation, independent final certification and kernel replay. The verification gates below check correctness separately. All completed samples, outliers, failures and measurement flags are retained.

## Full-system comparisons

One thread, one leased CPU per campaign, grevlex, degree scheduling, fixed resource caps, adjacent AB then BA. F₂ uses ordinary polynomial rings, including squares, with binary pivots explicitly enabled and dense pivots disabled in both arms. Odd-prime inputs use both archived drivers’ default disabled pivot policies. Every successful comparison matches the full reduced basis, all structural counters and all other output metadata. Only work and allocation differ, by the bitmap’s explicit payload growth.

| Implementation and campaign | Process B/A | Family-balanced B/A | Candidate B/A | CPU | Peak RSS A/B KiB |
| --- | ---: | ---: | ---: | ---: | ---: |
| bitmap: f2-false | 1.028885 | 1.044796 | 1.015296 | 85 | 90288/97644 |
| bitmap: f2-false-repeat | 1.149102 | 1.190550 | 0.966261 | 44 | 88240/97640 |
| bitmap: prime-control | 1.030909 | 1.030909 | 1.024153 | 95 | 77968/79692 |
| bitmap: prime-control-repeat | 1.056542 | 1.056542 | 1.017445 | 30 | 78396/79676 |
| prototype: f2-false | 0.958300 | 0.972141 | 0.966215 | 2 | 92452/96176 |
| prototype: f2-false-repeat | 0.949186 | 0.958731 | 0.964028 | 40 | 90196/96176 |
| prototype: prime-control | 0.981168 | 0.981168 | 1.005144 | 64 | 77488/79792 |
| prototype: prime-control-repeat | 0.982784 | 0.982784 | 0.989767 | 76 | 75164/74068 |
| selected: f2-false | 0.986598 | 1.001789 | 0.977486 | 12 | 89196/86032 |
| selected: f2-false-repeat | 0.989865 | 0.999606 | 0.996184 | 76 | 92092/87972 |
| selected: prime-control | 0.974816 | 0.974816 | 0.967556 | 63 | 82184/83892 |
| selected: prime-control-repeat | 0.978807 | 0.978807 | 0.972332 | 80 | 81916/83880 |

The selected F₂ family-balanced results do not establish an overall speedup. The selected odd-prime process observations are about 2–3% lower, with per-family variability and regressions retained below. These small development sweeps do not establish the SPEC’s solved-coverage, held-out or leadership requirements.

Each F₂ campaign contains 40 processes/20 comparisons across 8 families; each odd-prime campaign contains 56 processes/28 comparisons across 7 families. There are no failed processes, timeouts or basis mismatches in these campaigns. The bitmap-only and batched prototypes share an experimental packed-table baseline. The selected comparison uses the packed-pivot implementation from PR #11030 and excludes the experimental metadata, known-pivot projection and XOR tables. Prototype and selected ratios measure different complete implementations and must not be multiplied.

| Selected campaign/family | Initial process B/A | Repeat process B/A |
| --- | ---: | ---: |
| F₂: cyclic | 0.864026 | 0.988835 |
| F₂: kat | 1.856554 | 1.016904 |
| F₂: eco | 1.001751 | 0.979207 |
| F₂: noon | 1.077550 | 1.048510 |
| F₂: reimer | 0.292330 | 1.000570 |
| F₂: minrank | 2.932256 | 1.028386 |
| F₂: dense-quadratic | 0.736386 | 0.985849 |
| F₂: mq | 0.928105 | 0.951843 |
| Odd prime: cyclic | 0.982489 | 0.991832 |
| Odd prime: kat | 0.902273 | 0.983893 |
| Odd prime: eco | 0.941972 | 0.967940 |
| Odd prime: noon | 0.996029 | 0.982395 |
| Odd prime: reimer | 0.953411 | 0.946754 |
| Odd prime: minrank | 1.042305 | 0.990914 |
| Odd prime: dense-quadratic | 1.012063 | 0.988750 |

## Queue kernel

Same frozen prototype executable for both arms: portable versus native support queue, including bitmap initialization, slice validation, output validation and complete structural hashing. Input generation is excluded. Three interleaved occurrences of each ID exercise both insertion and repeated membership. The fixed cost model is linear. The initial matched run targets 1 second per point; the single longer repeat targets 8 seconds. Kernel ratios do not predict full-system speedups.

| Arena IDs | Initial native/portable | Initial flags | Longer native/portable | Longer flags |
| ---: | ---: | ---: | ---: | ---: |
| 256 | 0.192726 | 2 | 0.210472 | 0 |
| 1024 | 0.167411 | 0 | 0.147121 | 0 |
| 4096 | 0.157096 | 0 | 0.176194 | 0 |
| 16384 | 0.273016 | 4 | 0.117118 | 0 |
| 65536 | 0.264608 | 3 | 0.287953 | 1 |

The shared filesystem filled during the longer run after seven completed arms. Those samples remain unchanged; only unfinished arms resumed, using the original leased CPU. The same event interrupted a prototype usage check, an integration build and a frozen checkout. Original failure logs are retained. Fresh recovered verification runs and the recovered frozen carrier supply the successful checks; no completed timing sample was discarded or repeated.

## Verification and provenance

Measurements use the shared host `chungus2`, an AMD EPYC 9455 48-Core Processor, with Lean 4.35.0-rc3. The queue operation itself uses scalar exact byte/word operations; matrix SIMD dispatch options and full compiler manifests are retained in every capsule.

Each stage has twelve passing ASan/UBSan variants: Clang 23.1.3 and GCC 16.2.0, automatic/AVX2/scalar paths with wide-product and remainder implementations. The native batch stages assert actual instrumented calls and check malformed slices, duplicate IDs, byte boundaries, shared and exclusive ownership, borrowed aliases and marked-linear buffers. The selected stage also passes the library/theory build, independent SymPy and Singular oracles (567 bases each), driver checks, benchmark verification, DAG, phase, release-manifest, copyright and line-count gates. Kernel replay and axiom audits remain separate from native verification.

- bitmap: runtime `1778a37c808c`, checks `ce04179984dd`; native compiler clang version 21.1.8; generated Lean C compiler clang version 23.1.0 (https://github.com/llvm/llvm-project ea7d852a70e8bdfaf601d6626a760f9771b2c4b4).
  Capsule [f4-symbolic-bitmap-1778a37c808c.tar.xz](raw/f4-symbolic-bitmap-1778a37c808c.tar.xz), SHA-256 `3d1c777609ca30c9ada3b60955164ff247e999d96138fceb75ac01dbdd848d43`.
- prototype: runtime `531625070811`, checks `db7440bd4148`; native compiler clang version 21.1.8; generated Lean C compiler clang version 23.1.0 (https://github.com/llvm/llvm-project ea7d852a70e8bdfaf601d6626a760f9771b2c4b4).
  Capsule [f4-support-native-531625070811.tar.xz](raw/f4-support-native-531625070811.tar.xz), SHA-256 `9fe99522eb2b51db231ab107efd568179e987fd5a50d25bb027f9fb8c160fd23`.
- selected: runtime `f2430e4fd007`, checks `4ffcccb59166`; native compiler clang version 21.1.8; generated Lean C compiler clang version 23.1.0 (https://github.com/llvm/llvm-project ea7d852a70e8bdfaf601d6626a760f9771b2c4b4).
  Capsule [f4-support-integration-f2430e4fd007.tar.xz](raw/f4-support-integration-f2430e4fd007.tar.xz), SHA-256 `22bc2936860916bddcf8940c78dc43f30880b77d03355a86b27a146aaf4e98da`.

Regenerate and validate every source blob, check snapshot, output, counter, input hash, compiler manifest, timing ratio and kernel hash:

`python3 scripts/bench/groebner_support_report.py --bitmap reports/bench-results/raw/f4-symbolic-bitmap-1778a37c808c.tar.xz --prototype reports/bench-results/raw/f4-support-native-531625070811.tar.xz --selected reports/bench-results/raw/f4-support-integration-f2430e4fd007.tar.xz --output reports/bench-results/hexgroebner-support.md --check --current`
