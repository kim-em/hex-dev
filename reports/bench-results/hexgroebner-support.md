# Symbolic support queues

Support batching preserves the first-occurrence queue order and the complete reduced basis. A dynamically growing arena bitmap replaces support hash lookup; a bounded native operation validates at most 4096 u32 IDs before updating the bitmap and pending queue. The portable definition has the same result, rejection and ownership contract. The workspace reuses a grow-only bitmap across preparations and checkpoints. Growth is charged once to work and packed bytes; the next preparation clears only visited IDs and charges their clearing work. The pending queue still uses Lean’s array of natural numbers; this change does not establish fully packed F4 scheduling storage.

These are shared-host development measurements, not a fastest-open-source milestone. Candidate production excludes certificate generation, independent final certification and kernel replay. The verification gates below check correctness separately. All completed samples, outliers, failures and measurement flags are retained.

## Full-system comparisons

One thread, one leased CPU per campaign, grevlex, degree scheduling, fixed resource caps, adjacent AB then BA. F₂ uses ordinary polynomial rings, including squares, with binary pivots explicitly enabled and dense pivots disabled in both arms. Odd-prime inputs use both archived drivers’ default disabled pivot policies. Every successful comparison matches the full reduced basis, all structural counters and all other output metadata. Only work and allocation differ: the first three stages charge fresh bitmap growth per preparation; the reused and owned stages charge growth once plus clearing work.

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
| reused: f2-false | 1.026100 | 1.074681 | 1.160092 | 57 | 92260/93432 |
| reused: f2-false-repeat | 0.960050 | 1.031904 | 0.887985 | 34 | 92200/94108 |
| reused: prime-control | 0.956757 | 0.956757 | 1.007979 | 80 | 73180/75252 |
| reused: prime-control-repeat | 1.034786 | 1.034786 | 1.122743 | 69 | 72540/77300 |
| owned: f2-false | 0.987795 | 0.996180 | 0.989233 | 34 | 92220/81992 |
| owned: f2-false-repeat | 0.995024 | 1.006394 | 0.998746 | 41 | 92220/82216 |
| owned: prime-control | 0.950269 | 0.950269 | 0.959041 | 43 | 82088/74052 |
| owned: prime-control-repeat | 0.975302 | 0.975302 | 0.954718 | 3 | 81980/74056 |

Fields in f2-false: 2.

Fields in prime-control: 32003, 2147483647.

Stage definitions: bitmap uses portable bitmap membership with fresh scratch per preparation; prototype adds bounded native queueing against the experimental table baseline; selected ports fresh native bitmap queueing to the packed-pivot main implementation; reused retains scratch but still shares the outer round workspace; owned moves the workspace through round boundaries and consumes the visited queue during sorting. The owned comparison measures this complete package, including any effect on other workspace buffers; it does not isolate bitmap ownership as the cause of an F4 timing difference.

| Campaign | Minimum process B/A | Median process B/A | Maximum process B/A |
| --- | ---: | ---: | ---: |
| bitmap: f2-false | 0.647932 | 1.029026 | 1.556040 |
| bitmap: f2-false-repeat | 0.179834 | 0.978949 | 10.895640 |
| bitmap: prime-control | 0.768653 | 1.001558 | 1.757749 |
| bitmap: prime-control-repeat | 0.510840 | 0.988612 | 1.967835 |
| prototype: f2-false | 0.648037 | 0.978060 | 1.340300 |
| prototype: f2-false-repeat | 0.721058 | 0.942971 | 1.263822 |
| prototype: prime-control | 0.476407 | 0.991446 | 1.457603 |
| prototype: prime-control-repeat | 0.396445 | 0.933977 | 1.987766 |
| selected: f2-false | 0.134393 | 0.973540 | 7.340029 |
| selected: f2-false-repeat | 0.824024 | 0.979210 | 1.334151 |
| selected: prime-control | 0.397130 | 0.973274 | 1.662219 |
| selected: prime-control-repeat | 0.805761 | 0.974553 | 1.204386 |
| reused: f2-false | 0.456089 | 0.957368 | 8.565740 |
| reused: f2-false-repeat | 0.412822 | 0.936519 | 3.328009 |
| reused: prime-control | 0.448273 | 0.990027 | 1.795695 |
| reused: prime-control-repeat | 0.438244 | 0.998684 | 4.405475 |
| owned: f2-false | 0.823315 | 0.979757 | 1.263369 |
| owned: f2-false-repeat | 0.819336 | 0.982009 | 1.297282 |
| owned: prime-control | 0.220640 | 0.979552 | 2.389706 |
| owned: prime-control-repeat | 0.856708 | 0.975787 | 1.145598 |

The owned F₂ family-balanced observations remain near parity. Its odd-prime process observations are lower in both campaigns, but these are shared-host observations on the fixed development suite, with per-family variation retained below; no general speed or leadership claim follows.

The earlier reused stage has mixed process observations and does not establish an overall F₂ or odd-prime speedup. The resource benefit is verified separately: repeated preparations and separate-tail remainders reuse paid-for bitmap payload, and the owned stage checks zero bitmap copies through fresh public deterministic, sampled and certificate-producing computations (the conservative counter also includes column-map zero-fill copies) in all twelve sanitizer variants. The earlier reused stage checked only direct exclusive-workspace preparations; its outer-loop sharing is excluded from that zero-copy claim.

The original selected F₂ family-balanced results do not establish an overall speedup. The original selected odd-prime process observations are about 2–3% lower, with per-family variability and regressions retained below. These small development sweeps do not establish the SPEC’s solved-coverage, held-out or leadership requirements.

Each F₂ campaign contains 40 processes/20 comparisons across 8 families; each odd-prime campaign contains 56 processes/28 comparisons across 7 families. There are no failed processes, timeouts or basis mismatches in these campaigns. The bitmap-only and batched prototypes share an experimental packed-table baseline. The selected, reused and owned comparisons use the packed-pivot implementation from PR #11030 and exclude the experimental metadata, known-pivot projection and XOR tables. Prototype and selected ratios measure different complete implementations and must not be multiplied.

| Owned campaign/family | Initial process B/A | Repeat process B/A |
| --- | ---: | ---: |
| F₂: cyclic | 0.992723 | 0.982008 |
| F₂: kat | 1.023651 | 1.061655 |
| F₂: eco | 0.975471 | 0.984573 |
| F₂: noon | 1.019878 | 1.014326 |
| F₂: reimer | 0.993867 | 0.993885 |
| F₂: minrank | 1.008247 | 1.062544 |
| F₂: dense-quadratic | 1.002493 | 1.006561 |
| F₂: mq | 0.954955 | 0.950814 |
| Odd prime: cyclic | 0.977725 | 0.972053 |
| Odd prime: kat | 0.981581 | 0.977552 |
| Odd prime: eco | 0.971085 | 0.973612 |
| Odd prime: noon | 0.700129 | 0.972909 |
| Odd prime: reimer | 1.136124 | 0.932756 |
| Odd prime: minrank | 0.958697 | 1.005225 |
| Odd prime: dense-quadratic | 0.984559 | 0.994611 |

The current completed runs charge 1–4778 additional logical bitmap bytes per computation. These counters describe payload growth, not process RSS or allocator capacity.

External callers may retain a checkpoint or share raw buffers; those observers require ordinary copy-on-write to preserve their snapshots. The zero-copy assertions cover fresh complete computations and exclusive direct preparations. They do not promise zero copies for externally retained snapshots.

| Owned family/field | Initial baseline process ms | Repeat baseline process ms | Initial candidate B/A | Repeat candidate B/A |
| --- | ---: | ---: | ---: | ---: |
| F₂: cyclic | 128.161 | 129.885 | 0.982214 | 0.974800 |
| F₂: kat | 4.651 | 4.764 | 1.047982 | 1.035100 |
| F₂: eco | 95.584 | 96.452 | 0.975645 | 0.983824 |
| F₂: noon | 4.560 | 4.688 | 1.063514 | 1.111602 |
| F₂: reimer | 3.566 | 3.786 | 1.042421 | 0.997617 |
| F₂: minrank | 4.166 | 4.279 | 0.961149 | 1.088909 |
| F₂: dense-quadratic | 6.628 | 6.725 | 0.970292 | 0.970687 |
| F₂: mq | 262.225 | 264.044 | 0.952545 | 0.946784 |
| Odd prime: cyclic | 210.635 | 215.589 | 0.978521 | 0.970931 |
| Odd prime: kat | 25.710 | 28.185 | 0.973968 | 0.950431 |
| Odd prime: eco | 816.401 | 819.157 | 0.975364 | 0.973523 |
| Odd prime: noon | 21.093 | 18.139 | 0.716016 | 0.950720 |
| Odd prime: reimer | 84.424 | 77.950 | 1.061222 | 0.907406 |
| Odd prime: minrank | 6.781 | 7.863 | 1.092060 | 0.963007 |
| Odd prime: dense-quadratic | 10.668 | 10.208 | 0.967396 | 0.968694 |

Baseline absolute values above are medians of the retained process samples, including startup and full output. Extreme ratios in short cases cannot identify small algorithm effects. Peak RSS changes include runtime/allocator behavior and are not attributed to bitmap size; the logical bitmap payload is charged separately. Portable primitive timings are reported separately from full native-enabled F4; no portable full-system speed claim is made.

## Queue kernel

Same frozen prototype executable for both arms: portable versus native support queue, including bitmap initialization, slice validation, output validation and complete structural hashing. Input generation is excluded. Three interleaved occurrences of each ID exercise both insertion and repeated membership. The fixed cost model is linear. The initial matched run targets 1 second per point; the single longer repeat targets 8 seconds. Kernel ratios do not predict full-system speedups. These original kernel measurements refer to the prototype and original selected queue sources, whose exact blob IDs match; the ownership revision is measured separately below. Exit code 2 denotes a retained inconclusive timing verdict when the computation and full output checks succeed.

| Arena IDs | Initial native/portable | Initial flags | Longer native/portable | Longer flags |
| ---: | ---: | ---: | ---: | ---: |
| 256 | 0.192726 | 2 | 0.210472 | 0 |
| 1024 | 0.167411 | 0 | 0.147121 | 0 |
| 4096 | 0.157096 | 0 | 0.176194 | 0 |
| 16384 | 0.273016 | 4 | 0.117118 | 0 |
| 65536 | 0.264608 | 3 | 0.287953 | 1 |

## Ownership controls

A separate non-timed Clang ASan/UBSan diagnostic runs the same public-route tests against the owned source and a control restoring only the three outer-loop files from the reused stage. The queue/clear provider and public test bodies match the archived verified sources. Pending-array sharing is counted separately. As in the ordinary native harness, leak detection is disabled for the Lean/runtime loader; address and undefined-behavior checks remain enabled.

| Route | Owned queue/clear/copies | Restored-loop queue/clear/copies | Pending-array copies owned/control |
| --- | --- | --- | --- |
| Deterministic | 10/3/0 | 10/3/3 | 0/0 |
| Sampled | 10/3/0 | 10/3/0 | 0/0 |
| Certificate producer | 10/3/0 | 10/3/3 | 0/0 |

The control detects the original deterministic and producer copies. The sampled small case was already copy-free, so its control is retained as zero. This checks the queue-call ownership; the in-place sorting conclusion additionally comes from inspection of the generated C. An initial standalone run used different leak-check settings and reported 320 bytes with an allocation frame in the runtime loader; its output is retained. A later diagnostic assertion incorrectly expected copies on every restored route; the successful CSV is retained and the final check validates the observed deterministic/producer regression without rerunning completed executions.
Control capsule [f4-support-owner-controls-e7360335bbe2.tar.xz](raw/f4-support-owner-controls-e7360335bbe2.tar.xz), SHA-256 `dcfa4f12e4f9a830fa5f3b36aa40810be7bdaece68159b7c5c457159834a576a`.


## Current queue versus HashSet

The owned implementation adds a direct primitive comparison with the original per-term HashSet membership loop, including insertion and rehashing. Both arms produce and validate the same first-occurrence ordered queue and hash that complete result. The bitmap arm includes initialization and bounded native calls. This isolated primitive allocates fresh membership storage in both arms; workspace reuse is covered by the full-system comparison and allocation assertions. Four-second targets, AB/BA order and every flag are retained.

| Arena IDs | Bitmap/HashSet | Flags |
| ---: | ---: | ---: |
| 256 | 0.269750 | 0 |
| 1024 | 0.251592 | 0 |
| 4096 | 0.234161 | 0 |
| 16384 | 0.258002 | 0 |
| 65536 | 0.367800 | 0 |

Four retained AB/BA user-cycle profiles examine the earlier bitmap-only result on the largest MQ input. The original HashSet support loop accounts for 8.87–9.51% of sampled self cycles, while the portable bitmap queue loop accounts for 5.10–6.60%. Monomial preparation, product lookup and matrix projection remain large costs. This diagnostic does not explain the extreme short-process timing ratios or establish their cause; it does not support a language-impossibility conclusion. The profile metadata, source/executable identities, reports, headers and trace hashes are retained separately from timing samples.

The shared filesystem filled during the longer run after seven completed arms. Those samples remain unchanged; only unfinished arms resumed, using the original leased CPU. The 16384-ID block 0 A/B pair was split by this interruption; its ratio includes that gap and is not an uninterrupted adjacent comparison. The same event interrupted a prototype usage check, an integration build and a frozen checkout. Original failure logs are retained. Fresh recovered verification runs and the recovered frozen carrier supply the successful checks; no completed timing sample was discarded or repeated.

## Verification and provenance

Measurements use the shared host `chungus2`, an AMD EPYC 9455 48-Core Processor, with Lean 4.35.0-rc3. The queue operation itself uses scalar exact byte/word operations; matrix SIMD dispatch options and full compiler manifests are retained in every capsule.

Each stage has twelve passing ASan/UBSan variants: Clang 23.1.3 and GCC 16.2.0, automatic/AVX2/scalar paths with wide-product and remainder implementations. The native batch stages assert actual instrumented calls and check malformed slices, duplicate IDs, byte boundaries, shared and exclusive ownership, borrowed aliases and marked-linear buffers. The selected, reused and owned stages also pass the library/theory build, independent SymPy and Singular oracles (567 bases each), driver checks, benchmark verification, DAG, phase, release-manifest, copyright and line-count gates. Kernel replay and axiom audits remain separate from native verification.

- bitmap: runtime `1778a37c808c`, checks `ce04179984dd`; native compiler clang version 21.1.8; generated Lean C compiler clang version 23.1.0 (https://github.com/llvm/llvm-project ea7d852a70e8bdfaf601d6626a760f9771b2c4b4).
  Capsule [f4-symbolic-bitmap-1778a37c808c.tar.xz](raw/f4-symbolic-bitmap-1778a37c808c.tar.xz), SHA-256 `3d1c777609ca30c9ada3b60955164ff247e999d96138fceb75ac01dbdd848d43`.
- prototype: runtime `531625070811`, checks `db7440bd4148`; native compiler clang version 21.1.8; generated Lean C compiler clang version 23.1.0 (https://github.com/llvm/llvm-project ea7d852a70e8bdfaf601d6626a760f9771b2c4b4).
  Capsule [f4-support-native-531625070811.tar.xz](raw/f4-support-native-531625070811.tar.xz), SHA-256 `9fe99522eb2b51db231ab107efd568179e987fd5a50d25bb027f9fb8c160fd23`.
- selected: runtime `f2430e4fd007`, checks `4ffcccb59166`; native compiler clang version 21.1.8; generated Lean C compiler clang version 23.1.0 (https://github.com/llvm/llvm-project ea7d852a70e8bdfaf601d6626a760f9771b2c4b4).
  Capsule [f4-support-integration-f2430e4fd007.tar.xz](raw/f4-support-integration-f2430e4fd007.tar.xz), SHA-256 `22bc2936860916bddcf8940c78dc43f30880b77d03355a86b27a146aaf4e98da`.
- reused: runtime `0a8df82a5c94`, checks `29f795cdd154`; native compiler clang version 21.1.8; generated Lean C compiler clang version 23.1.0 (https://github.com/llvm/llvm-project ea7d852a70e8bdfaf601d6626a760f9771b2c4b4).
  Capsule [f4-support-reuse-0a8df82a5c94.tar.xz](raw/f4-support-reuse-0a8df82a5c94.tar.xz), SHA-256 `29d61d074f4d3b0fdb1514fe7b19a64c4f5d4197cd20670af15a330a0a282971`.
- owned: runtime `e7360335bbe2`, checks `5b6ffbe2bcb2`; native compiler clang version 21.1.8; generated Lean C compiler clang version 23.1.0 (https://github.com/llvm/llvm-project ea7d852a70e8bdfaf601d6626a760f9771b2c4b4).
  Capsule [f4-support-owner-e7360335bbe2.tar.xz](raw/f4-support-owner-e7360335bbe2.tar.xz), SHA-256 `7ac48258349029597cad414037d969725868da80f01e77da632979c55940ddee`.

Regenerate and validate every source blob, check snapshot, output, counter, input hash, compiler manifest, timing ratio and kernel hash:

`python3 scripts/bench/groebner_support_report.py --bitmap reports/bench-results/raw/f4-symbolic-bitmap-1778a37c808c.tar.xz --prototype reports/bench-results/raw/f4-support-native-531625070811.tar.xz --selected reports/bench-results/raw/f4-support-integration-f2430e4fd007.tar.xz --reused reports/bench-results/raw/f4-support-reuse-0a8df82a5c94.tar.xz --owned reports/bench-results/raw/f4-support-owner-e7360335bbe2.tar.xz --controls reports/bench-results/raw/f4-support-owner-controls-e7360335bbe2.tar.xz --output reports/bench-results/hexgroebner-support.md --check --current`
