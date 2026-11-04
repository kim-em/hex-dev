# Private packed pivots over ordinary F2

An explicit `binaryPivots` option uses private packed pivots and an accumulator in bounded untraced matrix frames. It defaults to false. The deterministic driver accepts `--binary-pivots true|false` and reports the requested policy. Ordinary polynomial exponents retain their usual meaning; no Boolean-quotient relation is introduced.

The selected implementation uses sparse toggles or word XOR according to row density, skips zero prepaid scan blocks, and gathers output with word masks and set-bit iteration. The transparent provider retains the sparse reference result, including every logical counter. Private payload must fit alongside the complete reference payload in the packed-byte allowance. A payload decline may repeat work in the reference continuation; the speculation bound is per frame.

Manual shared-host comparisons use one algorithm thread, one automatically leased CPU, and adjacent AB then BA. All completed samples, failures, warnings, variability and RSS remain retained. Every full F4 comparison below checks complete bases and all logical statistics. These development suites are not held-out acceptance inputs.

| Comparison | Process B/A | Candidate B/A | Equal-family B/A | Pair range | CPU |
|---|---:|---:|---:|---:|---:|
| packed / prior | 0.896568 | 0.879461 | 0.950482 | 0.549846–1.261359 | 41 |
| packed / prior repeat | 0.885916 | 0.876377 | 0.936964 | 0.543308–1.261592 | 78 |
| word cursor / packed | 0.998665 | 1.221873 | 0.982611 | 0.423207–3.737744 | 42 |
| word cursor / packed repeat | 0.962978 | 0.932672 | 0.939315 | 0.618980–1.626866 | 83 |
| zero blocks / packed | 0.956618 | 0.973326 | 0.970228 | 0.470078–1.323015 | 19 |
| zero blocks / packed repeat | 0.970971 | 1.047719 | 0.979795 | 0.695492–1.958797 | 64 |
| odd-prime control | 1.008887 | 1.025450 | 1.008887 | 0.870294–1.219917 | 39 |

The word cursor variant is retained as an experiment. The selected zero-block scanner preserves the bitwise scan on nonzero blocks. Each variant has exactly one unchanged F2 repeat; no further unchanged F4 timing is collected.

| Family | Packed first/repeat | Word cursor first/repeat | Zero blocks first/repeat |
|---|---:|---:|---:|
| cyclic | 0.906528/0.911694 | 0.859511/0.930743 | 1.054079/0.865107 |
| kat | 1.027293/1.023144 | 1.052154/0.910863 | 0.747018/1.062883 |
| eco | 0.925292/0.927137 | 0.875347/0.728749 | 0.964177/0.922437 |
| noon | 1.030540/0.973532 | 2.014760/1.006674 | 0.840284/1.030094 |
| reimer | 1.045464/0.976399 | 0.674597/1.017733 | 1.058859/0.982914 |
| minrank | 1.018455/1.024263 | 0.804387/0.877030 | 1.129311/0.769130 |
| dense-quadratic | 0.992520/0.996309 | 0.942402/1.026255 | 1.138554/1.373117 |
| mq | 0.709808/0.708062 | 1.065547/1.063745 | 0.904061/0.936463 |

The two MQ ratios in the zero-blocks column are below one, but effects this size are not established against the variability observed across campaigns. Several small-family ratios also vary substantially. These observations do not establish a full-system improvement, justify a universal default or assert overall performance leadership.

The registered `binaryEliminate` and `binaryEliminateSparse` kernels use identical prepared F2 matrices with known reducers and dense targets. Timed work includes validation, workspace construction, elimination, complete decoded rows and counters, and structural hashing. Preparation is outside timing. Both arms use the same executable; complete result hashes agree.

| Matrix parameter | Short-pass packed/sparse | Short floor flags / 4 | Longer-pass packed/sparse | Longer floor flags / 4 |
|---|---:|---:|---:|---:|
| 32 | 0.507179 | 4 | 0.524407 | 0 |
| 64 | 0.442849 | 4 | 0.446125 | 0 |
| 128 | 0.439586 | 4 | 0.373665 | 0 |
| 256 | 0.310990 | 4 | 0.319109 | 1 |
| 512 | 0.194602 | 4 | 0.225609 | 0 |

The initial pass targets 0.5 seconds of inner work; its matched rows are below the measured signal threshold. One longer matched pass targets 16 seconds. Its remaining flagged row is retained and does not independently justify a timing claim. No further unchanged kernel pass is collected. The short pass also retains the fixed trial-major complexity runs. The sparse arm can admit whole frames at parameters 32 and 64; from 128 upward its target count necessarily exceeds the ordinary frame cap and it uses the phased continuation. The packed cost model is O(n³/64+n²) at fixed word width; scans, decoding and hashing may dominate these finite sizes. These ratios compare those complete providers at the stated sizes and do not establish a full-system speedup of the same size.

The independent msolve comparison uses the canonical F2 suite, one thread, full reduced grevlex output, commit `3672113ee2c696a2ac9c637636e0f7214f500ba1`, Clang 23.1.3 and `-O3 -march=native`. Hex native C uses Clang 21.1.8 and generated C uses SDK Clang 23.1.0; compiler/tuning differences remain part of this observed gap. Every comparison has 40 completed processes and 20 equal complete bases. Inputs and every Hex logical counter agree across these variants. All samples and outliers remain retained; no further unchanged comparator repeat is collected.

| Hex version / msolve | Process ratio | Equal-family ratio | Pair range | CPU |
|---|---:|---:|---:|---:|
| initial packed | 1.355897 | 1.251469 | 0.616421–2.529335 | 76 |
| selected | 2.350870 | 2.199843 | 0.649892–4.997356 | 72 |
| selected repeat | 2.036549 | 1.907506 | 0.791147–17.487616 | 29 |

The selected-binary comparisons show a larger remaining gap than the initial prototype campaign and substantial variability. They do not demonstrate leadership or establish a cause for the change across campaigns. Candidate production, certificate generation, independent native verification and kernel checking remain distinct; these timings measure candidate/process work only.

All twelve Clang/GCC ASan+UBSan variants pass on the measured carrier and final high-pivot test snapshot. All nine project gates pass after correcting only the sparse benchmark's adjacent cost-model comment. The verifier checks that exact one-line difference, both source identities, every archived source blob, and all status records. The initial phase-check failure is retained. The final compute and full-initialization executables are byte-identical to the timed zero-block binaries; the benchmark registrations add no computation-driver code.

Coverage includes nonempty frames beyond the old dimensions, high-index packed pivot reads, target-pivot reuse, scalar/word path counters, byte/word boundaries, ordinary F2 complete F4 calls, malformed rows, exact physical-work boundaries with nonzero entries, and resource/ownership tests. Independent oracles check 567 bases with SymPy and Singular. Native verification and kernel replay remain separate from candidate timings. No fastest-open-source milestone or language impossibility is established.

Native runtime `e02434ca3804`; documented runtime `586b40821cab`; checks `687b436b9355`.

The combined tree after the scheduling-policy merge has runtime `545c62af5b66` and checks `6aaf1938b886`. Its separate twelve sanitizer variants, nine project gates and twenty CLI policy checks pass. Its computation executables are byte-identical to the measured carrier. The benchmark executable changes through the sampled-policy dependency; the packed runtime and kernel definitions are unchanged. Kernel timings remain bound to the original benchmark executable; no additional timing repeat is used.

The final validation snapshot has runtime `e5f7b7d0de7e` and checks `f2899eb5dd80`. The admission archive is named by its checks fingerprint and uses that same final runtime/check snapshot.

The separate non-timed admission audit uses the exact ten timed F₂ inputs and flags. Its instrumented Clang 23 executable reproduces every complete basis and logical counter. All 108 attempted frames are accepted; shape, logical-work, physical-work and byte refusals are zero in this audit. Larger shapes can still decline under the documented caps. Counts are cumulative row visits, not distinct basis polynomials. Admission confirms path activity without establishing a timing effect.

| Family | Inputs | Accepted / attempted frames | Known row visits | Target row visits |
|---|---:|---:|---:|---:|
| cyclic | 1 | 29 / 29 | 7676 | 2977 |
| kat | 1 | 4 / 4 | 5 | 13 |
| eco | 1 | 23 / 23 | 16878 | 1827 |
| noon | 1 | 1 / 1 | 0 | 5 |
| reimer | 1 | 1 / 1 | 0 | 6 |
| minrank | 1 | 6 / 6 | 100 | 47 |
| dense-quadratic | 1 | 11 / 11 | 562 | 213 |
| mq | 3 | 33 / 33 | 70906 | 6613 |

The final validation adds measured buffer-size totals, target-built word-pivot reuse, 1024-target admission, and the exact logical-work boundary plus one entry. The retained initial diagnostic-probe compile failure is corrected by adding standard I/O declarations. The test measures byte-array payload lengths, excluding allocator headers, padding and RSS. The production elimination code and timed computation executables are unchanged.

A separate non-timed replay of the exact Clang sanitizer test executable exercises all diagnostic classifier branches: accepted=83, logical=2, other_possible_byte_refusal=34, other_without_byte_refusal=75, physical=2, shape=3. It includes a forced byte refusal with an allowance smaller than the required private buffer. The two other categories distinguish whether the conservative byte upper bound excludes a byte refusal; they do not identify every internal failure cause.

`f4-binary-pivots-initial-86ad4e3f842f.tar.xz`: SHA-256 `c637818a14b1754bc9ae6a4fb036482fc931a1f39c4c9800846bb044c0706029`.
`f4-binary-words-f3525392a594.tar.xz`: SHA-256 `922f2311a836e0eaea33995e5f56922a8693e7a71dbcc4e0660648e197beba7b`.
`f4-binary-blocks-a45acb9da3a9.tar.xz`: SHA-256 `dccdafe6932284afc917b41b7dfe1f8fa8925c36aecbb1e9ae8ccec1b5b1b74c`.
`f4-binary-selected-586b40821cab.tar.xz`: SHA-256 `4414107aa1ac7152c4a05fb9892d22c7a9d0bd73459fd01a3c097236147f47d4`.
`f4-binary-combined-545c62af5b66.tar.xz`: SHA-256 `7abae21344382843e9addfddf24702f298cdf33965ca78d86eaa6ffce3ccb928`.
`f4-binary-final-e5f7b7d0de7e.tar.xz`: SHA-256 `f7b8f3c9b406ac81a188dc9cd3b5c4dddfe2a04a509415424ae13e05925e51f4`.
`f4-binary-admission-f2899eb5dd80.tar.xz`: SHA-256 `164efe7210a899ac0a7086246a531c7d9974a16a7ad95c0fa5dcb8d916b0e152`.
`f4-binary-refusals-f2899eb5dd80.tar.xz`: SHA-256 `cb669baa92a5df4b58df0f5f86bf142e2a4f2b10841086ce43085d2b769c9f92`.

Regenerate with `python3 scripts/bench/groebner_binary_report.py --initial reports/bench-results/raw/f4-binary-pivots-initial-86ad4e3f842f.tar.xz --word reports/bench-results/raw/f4-binary-words-f3525392a594.tar.xz --blocked reports/bench-results/raw/f4-binary-blocks-a45acb9da3a9.tar.xz --selected reports/bench-results/raw/f4-binary-selected-586b40821cab.tar.xz --rebased reports/bench-results/raw/f4-binary-combined-545c62af5b66.tar.xz --guards reports/bench-results/raw/f4-binary-final-e5f7b7d0de7e.tar.xz --admission reports/bench-results/raw/f4-binary-admission-f2899eb5dd80.tar.xz --refusals reports/bench-results/raw/f4-binary-refusals-f2899eb5dd80.tar.xz --report reports/bench-results/hexgroebner-binary.md --check`. Add `--current` to bind the checkout.
