# Deterministic elimination below a sampling cutoff

The sampled candidate producer accepts an explicit minimum target count. Pair matrices below it use deterministic elimination after shared selection and symbolic preprocessing. The sealed continuation retains the cutoff and advanced random state. Deterministic batches consume parent allowances and no random words. The default cutoff is zero, preserving the existing policy; ordinary deterministic driver executables are byte-identical. Every output remains an unchecked candidate requiring independent complete-basis certification.

Manual shared-host observations use one algorithm thread, runtime auxiliary threads, an automatically leased CPU and adjacent AB followed by BA. All completed processes, failures, variability and RSS are retained. The prime policy comparison has one unchanged repeat; no other unchanged repeat is collected. Native C uses Clang 21.1.8 and generated C uses SDK Clang 23.1.0, with production AVX-512 disabled.

| Comparison | Process B/A | Candidate B/A | Equal-family B/A | Pair range | CPU | Peak RSS A/B KiB |
|---|---:|---:|---:|---:|---:|---:|
| deterministic-prime | 1.078739 | 1.144815 | 1.078739 | 0.746895–1.732661 | 11 | 80048/82088 |
| deterministic-prime-b32-z1 | 0.998832 | 1.055212 | 0.998832 | 0.678157–1.545667 | 80 | 78000/81960 |
| deterministic-prime-b128-z1 | 1.105406 | 1.176942 | 1.105406 | 0.579981–1.704204 | 42 | 80048/82088 |
| deterministic-prime-b128-z3 | 1.179615 | 1.191499 | 1.179615 | 0.833633–2.245293 | 62 | 80048/82088 |
| deterministic-f2 | 0.928686 | 0.971009 | 1.022388 | 0.523392–1.335974 | 27 | 82096/77864 |
| cutoff128-prime | 0.935892 | 0.881809 | 0.935892 | 0.643388–1.335731 | 75 | 82112/73920 |
| cutoff128-prime-repeat | 0.928597 | 0.873034 | 0.928597 | 0.647311–1.238331 | 76 | 82052/73860 |
| cutoff128-f2 | 0.989180 | 0.924603 | 0.965167 | 0.788268–1.361416 | 22 | 77956/77892 |

The first five rows compare sampled B against deterministic A. They retain a 2×2 prime-field comparison (block sizes 32/128 and one/three total zero tests) plus the F2 default. The final three rows compare cutoff 128 against cutoff zero within the same sampled executable: one zero test on prime fields, three on F2. Every complete reduced basis agrees. No sampling independence or probability bound is claimed for SplitMix64.

| Family | Prime cutoff first | Prime cutoff repeat | F2 cutoff |
|---|---:|---:|---:|
| cyclic | 0.971691 | 0.972570 | 0.960362 |
| kat | 1.033668 | 1.029740 | 1.024743 |
| eco | 1.010383 | 1.011566 | 0.848233 |
| noon | 0.741050 | 0.745975 | 1.043418 |
| reimer | 0.881872 | 0.879694 | 0.973801 |
| minrank | 0.988079 | 0.968580 | 0.925980 |
| dense-quadratic | 0.959708 | 0.924603 | 0.878537 |
| mq | — | — | 1.091354 |

The prime cutoff reduces observed time primarily on Noon and Reimer. The F2 MQ inputs regress, so the cutoff remains explicit and no default change is selected. The diagnostic suites are development inputs, not a balanced acceptance suite or held-out evaluation.

The current msolve comparison uses commit `3672113ee2c696a2ac9c637636e0f7214f500ba1`, Clang 23.1.3, `-O3 -march=native`, and `-g 2 -l 2 -t 1`. All 56 processes complete with 28 equal complete bases. Hex/msolve process geometric mean is 1.571857, range 0.706782–2.308362. Compiler/tuning differences are part of this observed gap. Candidate production, certificate generation, independent native verification and kernel checking remain separate; only candidate/process times are measured here. No fastest-open-source milestone is demonstrated.

| Family | Hybrid Hex/msolve |
|---|---:|
| cyclic | 2.176524 |
| kat | 1.900367 |
| eco | 1.196439 |
| noon | 1.681517 |
| reimer | 1.972246 |
| minrank | 0.979925 |
| dense-quadratic | 1.474157 |

Both initial and final checks pass all twelve Clang/GCC ASan+UBSan variants and all nine project gates. Independent oracles compare 567 unique reduced bases with both SymPy and Singular. Cutoff tests cover deterministic-only/no-draw operation, default and mixed policies, scheduling suspension, exhausted parent work and resumed policy identity. Twelve CLI checks cover both initializers, default/zero/huge cutoffs, repeated flags and malformed values. Full initialization is the same native arithmetic, not a portable arithmetic timing.

The retained diagnostic profiles comprise four completed Eco processes, one MQ process exhausted under an accidentally omitted larger matrix-entry limit, and four corrected MQ processes. The failed command/output is retained. Profiles explain costs and are not timing comparisons. Raw trace hashes and reports are archived; raw perf data remain in the measurement workspace.

Runtime `81e8adae40cd`; initial checks `d80557ce8396`; final checks `1391d0dd95e7`. `f4-sampler-hybrid-81e8adae40cd.tar.xz`: SHA-256 `fa886aa8dd6b211ad877929f899149486cfd5aa53adf70ee45f799edeabba957`. `f4-sampler-hybrid-checks-1391d0dd95e7.tar.xz`: SHA-256 `90722cf141d91b74b024c846b7fccaae68b832e8ef427ad99c99d57653434fd7`.

Regenerate with `python3 scripts/bench/groebner_hybrid_report.py --capsule reports/bench-results/raw/f4-sampler-hybrid-81e8adae40cd.tar.xz --guards reports/bench-results/raw/f4-sampler-hybrid-checks-1391d0dd95e7.tar.xz --report reports/bench-results/hexgroebner-hybrid.md --check`. Add `--current` to bind the checkout.
