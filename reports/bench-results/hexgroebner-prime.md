# Exact delayed elimination over prime fields

The measured runtime source is `c4cb8197a53d`. Opt-in `delayedReduction` covers every prime `3 ≤ p < 2^31`; it defaults to false. Small fields retain the UInt64 accumulator bound below `2^50`. Four-byte coefficients use residues modulo `p²`: a cell and product are each below `p²`, their sum is below `2p² < 2^63`, and one exact correction restores the bound while preserving the residue modulo `p`.

All 240 final full-system processes succeeded, and all 120 adjacent off/on pairs have identical complete reduced bases, metadata and logical counters. The fixed selection is the first primary size in ten families over F₂, 32003 and M31, with grevlex order and degree scheduling. Both arms use one frozen executable, one automatically leased CPU, batch size 1024, binary pivots enabled and dense pivots disabled. Arm order alternates AB/BA. These first-size observations do not cover the complete fixed balanced suite or held-out acceptance.

| Field | Candidate B/A geometric mean | Observed process B/A | Candidate pair range | Peak RSS A/B, KiB |
|---|---:|---:|---:|---:|
| 2 (unchanged-path control) | 0.9052 | 0.9500 | 0.0922–1.3159 | 34696/34696 |
| 32003 | 0.9554 | 0.9426 | 0.6928–1.7965 | 595960/520032 |
| 2147483647 | 0.9375 | 0.9717 | 0.6665–1.6422 | 690204/627748 |

F₂ is a null control: both arms use the same executable and arithmetic route. Its observed spread measures variability in this campaign, not an algorithmic gain or a calibrated confidence interval. Candidate production and process time are separate observations. Their aggregate ratios are descriptive point estimates: gains comparable to the unchanged-control fluctuation cannot be attributed to this option. No control-adjusted speedup or aggregate causal improvement is claimed. All completed samples and tiny-case outliers remain included; the pair range also includes differences between families. External limits are 300 seconds, 8 GiB address space and 256 MiB per output file, with the fixed corpus protocol’s recorded large parent work/memory allowances. The data do not establish admission or timing under library default budgets. The smallest F₂ candidate ratio, 0.0922, is kat8-2 in block 0 of the first sweep; it is retained as unchanged-path variability.

| In-sample KLYZ-12 field | Candidate B/A | Pair ratios |
|---|---:|---:|
| 2 (unchanged-path control) | 0.9181 | 0.9881, 1.0318, 0.7098, 0.9819 |
| 32003 | 0.7379 | 0.7563, 0.7041, 0.7406, 0.7519 |
| 2147483647 | 0.7081 | 0.6665, 0.7251, 0.7132, 0.7295 |

| Field excluding in-sample KLYZ | Candidate B/A geometric mean |
|---|---:|
| 32003 | 0.9832 |
| 2147483647 | 0.9672 |

Excluding KLYZ leaves nine equally weighted first-size families. Both full and excluding-KLYZ summaries retain every pair; this sensitivity comparison does not replace the fixed balanced suite.

The independent instrumented M31 producer accepted all 61 matrices, declined none and discarded zero charged native work; its complete output and counters equal production. This is evidence for that motivating system, not a guarantee against late refusals on other inputs. Work and private-payload caps can still trigger bounded refusal and continuation. Cancellation is observed between native calls.

| Delayed whole frame / ordinary continuation: field | Columns | B/A geometric mean |
|---|---:|---:|
| 251 | 1024 | 0.9158 |
| 251 | 2048 | 0.9205 |
| 251 | 4096 | 0.8821 |
| 32003 | 1024 | 0.9433 |
| 32003 | 2048 | 0.9658 |
| 32003 | 4096 | 0.9388 |
| 2147483647 | 1024 | 0.9493 |
| 2147483647 | 2048 | 0.9914 |
| 2147483647 | 4096 | 0.9135 |

The 42 final lean-bench processes retain all samples and have no point below the signal floor. Kernel sizes are 1024–4096 columns, below the 131072-column admission ceiling. A quadratic verdict on three sizes is a limited consistency observation, not a proof or evidence of scaling to that ceiling. The six three-trial, three-size sweeps give 2 verdicts consistent with quadratic work and 4 inconclusive verdicts. Both outcomes are retained; no proof of asymptotic behavior follows from this grid. Matched runs alternate AB/BA. Inputs have distinct known heads, dense tails and eight shared targets. Preparation is outside timing; validation, elimination and hashing complete row contents, labels and all eight counters are inside. Every matched digest agrees.

The host is AMD EPYC 9455. Production native code uses Clang 21.1.8; Lean SDK compilation uses Clang 23.1.0 and Lean 4.35.0-rc3. Guarded AVX2 and scalar fallbacks are enabled; experimental AVX-512 is disabled. Executable/compiler hashes, build flags, selected CPUs and host activity are retained in the manifests. Timing evidence comes from manual shared-host runs, never CI.

The earlier isolated prime-square prototype replay has B/A 0.8376 on four initial AB/BA provider observations. Its complete independent matrix comparison is outside the C monotonic timing interval. The retained frame is the highest-work input among progressive entry-maximum dumps, not the absolute maximum-work frame. The prototype executable and production runtime have distinct source and binary identities.

The archive also retains the unselected mixed-width and first split-width campaigns, including every outlier, plus a strict non-overlapping join of the initial four focused and 116 remaining processes. Their complete logical outputs agree with the final implementation under their recorded controls. They do not establish the combined dense-pivot option contract: the final implementation adds the missing 65536-column preparation guard and regression tests. A failed GCC test-counter macro build is retained; the final statement macro passes strict warnings on both compilers.

Final local verification includes twelve Clang/GCC ASan/UBSan variants; exact guard-page loads and per-width four-lane coverage; near-UInt64 and prime-square residue boundaries; direct scalar Lean comparisons; newly admitted reducer/target counts; exact work/byte refusal boundaries; combined M31 dense/delayed flags below and above 65536 columns; independent portable-reference comparisons; and all nine recorded project gates, including the independent oracles and downstream kernel replay. Runtime/check-source identities are preserved separately, including the test-only counter fix.

These observations measure unchecked candidate production or matrix elimination. Certificate generation, independent native certification, kernel checking and complete checked calls remain separate costs. The fastest-open-source milestone, solved-coverage acceptance, full balanced and held-out comparisons, parallel comparator sweeps and the overall-fastest gap remain open.

Production evidence: `f4-prime-current-c4cb8197a53d.tar.xz` (SHA-256 `43f61d415dd9a14859c3d88b6840b6c04c4d9298bf9c1aaa9a0d9e8928c74aaf`). Isolated replay evidence: `f4-delayed-m31-replay-fa4f77c3cf24.tar.xz` (SHA-256 `289d184211f8f2e7c14c039c5c86338b57b4902a115cbf2fef4aa7c36a195f63`). Payload manifests, source blobs, complete outputs, counters, controls, unique schedule positions and coverage are replayed by this report generator.
All nine recorded project gates passed, including independent oracles and downstream kernel replay.

The first 120-process system sweep was inconclusive because the unchanged-path control varied. Its sole unchanged repeat is combined with it here: all 240 samples contribute, with no filtering and no further unchanged system reruns.

Two earlier current-source small-kernel campaigns are retained as inconclusive: 11 and 17 completed processes, each stopping at a point below the signal floor. No third small-input rerun was taken. The 1024–4096 suite uses different inputs fixed and fully validated before timing. At all three larger sizes the ordinary arm declines whole-frame admission and uses bounded continuation while the delayed arm admits a whole frame; this comparison measures admission, dispatch, elimination and complete output hashing together. It does not isolate arithmetic or compare two admitted native frames. The retained small-input campaigns do not provide conclusive like-for-like kernel timing evidence. The archive includes the standalone large-input checker source, Lake configuration, pinned manifest, toolchain and complete build/run logs under large-input-check/.
