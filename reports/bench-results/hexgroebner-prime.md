# Exact delayed elimination over prime fields

The measured runtime source is `5365207cfb16`. Opt-in `delayedReduction` covers every prime `3 ≤ p < 2^31`; it defaults to false. Small fields retain the UInt64 accumulator bound below `2^50`. Four-byte coefficients use residues modulo `p²`: a cell and product are each below `p²`, their sum is below `2p² < 2^63`, and one exact correction restores the bound while preserving the residue modulo `p`.

All 120 final full-system processes succeeded, and all 60 adjacent off/on pairs have identical complete reduced bases, metadata and logical counters. The fixed selection is the first primary size in ten families over F₂, 32003 and M31, with grevlex order and degree scheduling. Both arms use one frozen executable, one automatically leased CPU, batch size 1024, binary pivots enabled and dense pivots disabled. Arm order alternates AB/BA. These first-size observations do not cover the complete fixed balanced suite or held-out acceptance.

| Field | Candidate B/A geometric mean | Process B/A geometric mean | Candidate pair range | Peak RSS A/B, KiB |
|---|---:|---:|---:|---:|
| 2 | 1.0177 | 0.9295 | 0.3577–4.6566 | 34660/34664 |
| 32003 | 0.8989 | 0.9368 | 0.6831–1.0127 | 600568/566988 |
| 2147483647 | 0.9326 | 0.9652 | 0.7166–1.2462 | 725448/638128 |

Candidate production and process time are separate observations. All completed samples and tiny-case outliers remain included; the pair range also includes differences between families. External limits are 300 seconds, 8 GiB address space and 256 MiB per output file, with the fixed corpus protocol’s recorded large parent work/memory allowances. The data do not establish admission or timing under library default budgets.

| In-sample KLYZ-12 field | Candidate B/A | Pair ratios |
|---|---:|---:|
| 32003 | 0.6968 | 0.6831, 0.7107 |
| 2147483647 | 0.7206 | 0.7166, 0.7246 |

The independent instrumented M31 producer accepted all 61 matrices, declined none and discarded zero charged native work; its complete output and counters equal production. This is evidence for that motivating system, not a guarantee against late refusals on other inputs. Work and private-payload caps can still trigger bounded refusal and continuation. Cancellation is observed between native calls.

| Kernel field | Columns | B/A geometric mean |
|---|---:|---:|
| 251 | 128 | 0.8980 |
| 251 | 256 | 0.9222 |
| 251 | 512 | 0.9376 |
| 32003 | 128 | 0.9250 |
| 32003 | 256 | 0.9547 |
| 32003 | 512 | 0.9700 |
| 2147483647 | 128 | 0.9442 |
| 2147483647 | 256 | 0.9562 |
| 2147483647 | 512 | 0.9692 |

The 42 final lean-bench processes retain all samples and have no point below the signal floor. Six three-trial, three-size sweeps are consistent with quadratic work. Matched runs alternate AB/BA. Inputs have distinct known heads, dense tails and eight shared targets. Preparation is outside timing; validation, elimination and hashing complete row contents, labels and all eight counters are inside. Every matched digest agrees.

The host is AMD EPYC 9455. Production native code uses Clang 21.1.8; Lean SDK compilation uses Clang 23.1.0 and Lean 4.35.0-rc3. Guarded AVX2 and scalar fallbacks are enabled; experimental AVX-512 is disabled. Executable/compiler hashes, build flags, selected CPUs and host activity are retained in the manifests. Timing evidence comes from manual shared-host runs, never CI.

The earlier isolated prime-square prototype replay has B/A 0.8376 on four initial AB/BA provider observations. Its complete independent matrix comparison is outside the C monotonic timing interval. The retained frame is the highest-work input among progressive entry-maximum dumps, not the absolute maximum-work frame. The prototype executable and production runtime have distinct source and binary identities.

The archive also retains the unselected mixed-width and first split-width campaigns, including every outlier, plus a strict non-overlapping join of the initial four focused and 116 remaining processes. Their complete logical outputs agree with the final implementation under their recorded controls. They do not establish the combined dense-pivot option contract: the final implementation adds the missing 65536-column preparation guard and regression tests. A failed GCC test-counter macro build is retained; the final statement macro passes strict warnings on both compilers.

Final local verification includes twelve Clang/GCC ASan/UBSan variants; exact guard-page loads and per-width four-lane coverage; near-UInt64 and prime-square residue boundaries; direct scalar Lean comparisons; newly admitted reducer/target counts; exact work/byte refusal boundaries; combined M31 dense/delayed flags below and above 65536 columns; independent oracles and downstream kernel replay; and all nine project gates. Runtime/check-source identities are preserved separately, including the test-only counter fix.

These observations measure unchecked candidate production or matrix elimination. Certificate generation, independent native certification, kernel checking and complete checked calls remain separate costs. The fastest-open-source milestone, solved-coverage acceptance, full balanced and held-out comparisons, parallel comparator sweeps and the overall-fastest gap remain open.

Production evidence: `f4-prime-square-5365207cfb16.tar.xz` (SHA-256 `d1168eca3c3d39d5f5be25e57500136ee457a1423c827ff237185e5a81f673fa`). Isolated replay evidence: `f4-delayed-m31-replay-fa4f77c3cf24.tar.xz` (SHA-256 `289d184211f8f2e7c14c039c5c86338b57b4902a115cbf2fef4aa7c36a195f63`). Payload manifests, source blobs, complete outputs, counters, controls, unique schedule positions and coverage are replayed by this report generator.
