# Deterministic elimination below a sampling cutoff

The sampled candidate producer accepts an explicit minimum target count. Pair matrices below it use deterministic elimination after shared selection and symbolic preprocessing. The sealed continuation retains the cutoff and advanced random state. Deterministic batches consume parent allowances and no random words. The default cutoff is zero, preserving the existing policy; ordinary deterministic driver executables are byte-identical. Every output remains an unchecked candidate requiring independent complete-basis certification.

Manual shared-host observations use one algorithm thread, runtime auxiliary threads, an automatically leased CPU and adjacent AB followed by BA. All completed processes, failures, variability and RSS are retained. The prime policy and direct hybrid-versus-deterministic comparisons each have one unchanged repeat; no further unchanged repeat is collected. Native C uses Clang 21.1.8 and generated C uses SDK Clang 23.1.0, with production AVX-512 disabled.

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
| hybrid-versus-deterministic-prime | 0.829623 | 0.788221 | 0.829623 | 0.362839–2.199633 | 37 | 79940/72208 |
| hybrid-versus-deterministic-prime-repeat | 1.034023 | 0.877068 | 1.034023 | 0.479128–4.442734 | 42 | 72468/57868 |

The first five rows compare sampled B against deterministic A on the parent runtime `ddde8c89c095`. They retain a 2×2 prime-field comparison (block sizes 32/128 and one/three total zero tests) plus the F2 default. The three cutoff128 rows compare cutoff 128 against cutoff zero within the same sampled executable: one zero test on prime fields, three on F2. These are separate campaigns on different binaries and leased CPUs: multiplying their ratios does not establish a hybrid-versus-deterministic speedup. The final two rows directly compare the hybrid cutoff 128 against deterministic F4, using the same runtime and one unchanged repeat. These observations remain specific to the development suite and shared host. Every complete reduced basis agrees. No sampling independence or probability bound is claimed for SplitMix64.

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

cutoff128-prime: observed lower time in cyclic, noon, reimer, minrank, dense-quadratic; observed higher time in kat, eco.

cutoff128-prime-repeat: observed lower time in cyclic, noon, reimer, minrank, dense-quadratic; observed higher time in kat, eco.

cutoff128-f2: observed lower time in cyclic, eco, reimer, minrank, dense-quadratic; observed higher time in kat, noon, mq.

| Family | First sampled calls A/B | Repeat sampled calls A/B | F2 sampled calls A/B |
|---|---:|---:|---:|
| cyclic | 104/36 | 104/36 | 54/20 |
| kat | 32/0 | 32/0 | 4/0 |
| eco | 76/20 | 76/20 | 40/10 |
| noon | 36/0 | 36/0 | 0/0 |
| reimer | 96/0 | 96/0 | 0/0 |
| minrank | 12/0 | 12/0 | 12/0 |
| dense-quadratic | 24/0 | 24/0 | 18/0 |
| mq | — | — | 54/28 |

The direct hybrid-versus-deterministic comparison is inconclusive: first process B/A 0.829623, unchanged repeat 1.034023. The opposite directions and broad pair ranges do not establish a speedup.

The call totals verify that the cutoff actually reduced sampling; they include all completed processes. The prime cutoff reduces observed time primarily on Noon and Reimer. The F2 MQ inputs regress, so the cutoff remains explicit and no default change is selected. The cutoff 128 was selected using these development inputs; it has no held-out validation or demonstrated optimality. The cutoff comparison contains only zero and 128; it is not a sweep establishing an optimal threshold. The diagnostic suites are development inputs, not a balanced acceptance suite or held-out evaluation. Sampling counters describe sampled batches only; there is no direct counter of deterministic fallback batches.

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

Both initial and final checks pass all twelve Clang/GCC ASan+UBSan variants and all nine project gates. Independent oracles compare 567 unique reduced bases with both SymPy and Singular. Cutoff tests cover deterministic-only/no-draw operation with identical ordinary statistics, a run with strictly fewer but nonzero sampled calls, mixed one-slice resumption, deterministic-batch exhaustion after random draws, sampled-matrix exhaustion after deterministic commit, scheduling suspension, exhaustion after symbolic preprocessing has submitted a deterministic matrix, exhausted parent work and resumed policy identity. Twelve archived CLI checks cover both initializers, default/zero/huge cutoffs, repeated flags and malformed values. The existing CI runner also checks zero/two huge cutoffs and malformed values on both initializers. A failed deterministic batch is selected again on retry: changing the resumed batch-size cap can change whether it crosses the cutoff. A pending sampled matrix retains its original selection. Full initialization is the same native arithmetic, not a portable arithmetic timing.

The retained diagnostic profiles comprise four completed Eco processes, one MQ process exhausted under an accidentally omitted larger matrix-entry limit, and four corrected MQ processes. The failed command/output is retained. Profiles explain costs and are not timing comparisons. Raw trace hashes and reports are archived; raw perf data remain in the measurement workspace.

Earlier checks remain retained and verified separately: `f4-sampler-hybrid-checks-1391d0dd95e7.tar.xz` (SHA-256 `90722cf141d91b74b024c846b7fccaae68b832e8ef427ad99c99d57653434fd7`), `f4-sampler-hybrid-checks-332b0af770f9.tar.xz` (SHA-256 `08b5415f628e1573c760466b83e206e17b0eed4951bab357fc6f113030be79f0`). They are superseded by the final checks below. Direct comparison capsule `f4-sampler-hybrid-direct-81e8adae40cd.tar.xz`: SHA-256 `2e9334892d09b72848a203a3bfba6556219e46c8b83b6e0db1906b02d4741a37`.

Runtime `81e8adae40cd`; initial checks `d80557ce8396`; final checks `776e84e4758c`. `f4-sampler-hybrid-81e8adae40cd.tar.xz`: SHA-256 `fa886aa8dd6b211ad877929f899149486cfd5aa53adf70ee45f799edeabba957`. `f4-sampler-hybrid-checks-776e84e4758c.tar.xz`: SHA-256 `2d34f263d435bec0fb9c472cfa54d32ca8c4fd79d6d92eff5be39827f8234257`.

Regenerate with `python3 scripts/bench/groebner_hybrid_report.py --capsule reports/bench-results/raw/f4-sampler-hybrid-81e8adae40cd.tar.xz --guards reports/bench-results/raw/f4-sampler-hybrid-checks-776e84e4758c.tar.xz --direct reports/bench-results/raw/f4-sampler-hybrid-direct-81e8adae40cd.tar.xz --report reports/bench-results/hexgroebner-hybrid.md --check`. Add `--current` to bind the checkout.
