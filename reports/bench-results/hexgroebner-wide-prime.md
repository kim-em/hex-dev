# Eight-lane wide-prime delayed updates

Frozen source `8b78fab53166` is compared directly with `45745225e6b0`. Four-byte coefficient updates use eight exact AVX-512F lanes only after CPU/OS capability checks and when a complete packet exists. Consecutive columns use unaligned vector loads/stores; other columns use gathers/scatters. AVX2 and portable fallbacks remain available. Each lane stays below p² after one correction because its sum is below 2p² < 2⁶³. Admission limits, row order, sugar labels and logical counters are preserved.

All 128 system processes and 64 adjacent AB/BA pairs have identical complete outputs and counters. The fixed selection covers the first primary size of ten families in all three fields, plus Eco-14/Eco-15 over F₂.

| Field | Candidate B/A | Process B/A | Candidate pair range | Peak RSS A/B, KiB |
|---|---:|---:|---:|---:|
| 2 | 1.0492 | 1.1759 | 0.5905–9.0519 | 34944/34812 |
| 32003 | 1.0546 | 1.0213 | 0.8387–4.3431 | 522628/526268 |
| 2147483647 | 0.9455 | 0.9670 | 0.3223–1.2498 | 600768/591784 |

These are descriptive point estimates on the shared AMD EPYC 9455 host. Unchanged F₂ and smaller-prime controls, every completed observation, outlier and failure are retained. No control-adjusted or multiplied-stage improvement is inferred. Runs use one leased CPU, one thread, degree scheduling, batch size 1024, binary pivots and delayed reduction enabled, and dense pivots disabled. Limits are 300 seconds, 8 GiB address space and 256 MiB output per process, with the fixed corpus’s explicit parent allowances. Native code uses Clang 21.1.8 and generated C uses SDK Clang 23.1.0 with Lean 4.35.0-rc3.

All nine project checks and 36 strict Clang/GCC sanitizer configurations are source-bound. Protected-page tests call the actual eight-lane kernel on three wide primes, contiguous/strided columns and packet/tail lengths. Both complete 1,134-case drivers, independent oracles, downstream replay and axiom audits remain distinct from candidate timings. The collector journals exact samples and publishes atomic checkpoints before its final analysis.


| Kernel | n | B/A pair ratios | Flagged samples |
|---|---:|---|---:|
| bulkDelayedWord | 128 | 0.9871, 0.9699 | 0/4 |
| bulkDelayedWord | 256 | 0.9684, 0.9721 | 0/4 |
| bulkDelayedWord | 512 | 0.9706, 0.9775 | 0/4 |
| bulkDelayedShort | 128 | 1.0252, 0.9920 | 0/4 |
| bulkDelayedShort | 256 | 0.9789, 1.0018 | 0/4 |
| bulkDelayedShort | 512 | 1.0017, 0.9913 | 1/4 |

Kernel comparisons use existing input schedules, one leased CPU, four-second batches, a 32-second batch cap and the unchanged ten-times-spawn signal floor. Complete output/counter hashes agree. Flagged observations are retained and do not support a speed claim. These matched samples do not establish empirical complexity acceptance.

Production stream SHA-256: `c39f8c84005e3165494e8d93be75171a672dc47ec739c3828fc052103e1edbb4`.

| Held-out family | Hex/msolve process ratio |
|---|---:|
| dense-quadratic | 1.1590 |
| sparse-structured | 0.9335 |
| positive-dimensional | 1.1091 |

The 27 held-out inputs have 108 successful processes and 54 equal complete bases. The family-balanced Hex/msolve process ratio is 1.0627×; peak RSS is 1340044/266108 KiB.

The comparator is msolve 3672113ee2c696a2ac9c637636e0f7214f500ba1, Clang 23.1.3, -O3 -march=native, full reduced output, linear algebra mode 2 and one thread. Candidate production excludes certificate generation, independent native certification and kernel checking. Full balanced solved coverage, equal-thread parallel comparisons, finite extensions, producer correctness/termination and fastest-open-source acceptance remain required by issue #10987. These data establish no language/runtime limitation. Scientific claims never rely on CI timing.

Held-out stream SHA-256: `e40e66f6d68296509c929d58c5af52bf674535ca4912f06a4baf94d9bea0823f`.
