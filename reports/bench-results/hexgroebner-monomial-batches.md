# Bounded monomial batch insertion

Product slices preflight up to 64 terms and 4096 charged work units in a private virtual table. Successful slices publish stable monomial identifiers, collision links, metadata and the final workspace together. Widening, rehashing, malformed representations and exhausted allowances defer the unchanged table. The portable contract and its scalar-equivalence theorem cover the expanded admission. Explicit borrowed aliases retain their contents; marked-linear copies preserve their mark.

Manual shared-host measurements use one algorithm thread, leased CPUs and adjacent AB followed by BA. Native C uses clang version 21.1.8; Lean-generated C uses SDK clang version 23.1.0. Production AVX-512 is disabled. All completed samples, variability, memory and failures are retained. Each inconclusive unchanged full-system campaign has at most one repeat. The revised source has separate observations after the alias fix.

| Source | Comparison | Process B/A | Candidate B/A | Equal-family B/A | Pair range | CPU | Peak RSS A/B KiB |
|---|---|---:|---:|---:|---:|---:|---:|
| 5943f8f79f43 | f2-false | 0.995899 | 0.885629 | 0.998274 | 0.808884–1.511234 | 18 | 90420/81948 |
| 5943f8f79f43 | f2-false-repeat | 0.987953 | 1.100517 | 0.991385 | 0.828621–1.237111 | 63 | 90336/82212 |
| 5943f8f79f43 | prime-control | 0.986544 | 0.914329 | 0.986544 | 0.615244–1.468055 | 19 | 80180/79836 |
| 5943f8f79f43 | prime-control-repeat | 0.970809 | 0.950516 | 0.970809 | 0.715497–1.175607 | 64 | 80080/80164 |
| ddde8c89c095 | f2-false | 0.987294 | 0.936923 | 0.987221 | 0.677801–1.321295 | 55 | 90180/81992 |
| ddde8c89c095 | f2-false-repeat | 1.005107 | 0.989491 | 1.013981 | 0.858599–1.306444 | 39 | 90088/81948 |
| ddde8c89c095 | prime-control | 0.985288 | 0.976422 | 0.985288 | 0.710700–1.285181 | 28 | 79940/79944 |
| ddde8c89c095 | prime-control-repeat | 0.981489 | 0.964764 | 0.981489 | 0.827214–1.243463 | 23 | 79848/79900 |

| Source / comparison | Family | Process B/A |
|---|---|---:|
| 5943f8f79f43 / f2-false | cyclic | 0.972029 |
| 5943f8f79f43 / f2-false | kat | 1.123665 |
| 5943f8f79f43 / f2-false | eco | 0.994254 |
| 5943f8f79f43 / f2-false | noon | 0.824006 |
| 5943f8f79f43 / f2-false | reimer | 1.023168 |
| 5943f8f79f43 / f2-false | minrank | 1.013163 |
| 5943f8f79f43 / f2-false | dense-quadratic | 1.077828 |
| 5943f8f79f43 / f2-false | mq | 0.986456 |
| 5943f8f79f43 / f2-false-repeat | cyclic | 0.952150 |
| 5943f8f79f43 / f2-false-repeat | kat | 1.002241 |
| 5943f8f79f43 / f2-false-repeat | eco | 0.973283 |
| 5943f8f79f43 / f2-false-repeat | noon | 1.078543 |
| 5943f8f79f43 / f2-false-repeat | reimer | 1.020555 |
| 5943f8f79f43 / f2-false-repeat | minrank | 0.959931 |
| 5943f8f79f43 / f2-false-repeat | dense-quadratic | 0.975881 |
| 5943f8f79f43 / f2-false-repeat | mq | 0.974344 |
| 5943f8f79f43 / prime-control | cyclic | 0.971130 |
| 5943f8f79f43 / prime-control | kat | 0.999222 |
| 5943f8f79f43 / prime-control | eco | 1.004464 |
| 5943f8f79f43 / prime-control | noon | 0.913121 |
| 5943f8f79f43 / prime-control | reimer | 0.974118 |
| 5943f8f79f43 / prime-control | minrank | 0.986839 |
| 5943f8f79f43 / prime-control | dense-quadratic | 1.063053 |
| 5943f8f79f43 / prime-control-repeat | cyclic | 0.967312 |
| 5943f8f79f43 / prime-control-repeat | kat | 1.003851 |
| 5943f8f79f43 / prime-control-repeat | eco | 0.985697 |
| 5943f8f79f43 / prime-control-repeat | noon | 0.993187 |
| 5943f8f79f43 / prime-control-repeat | reimer | 0.960525 |
| 5943f8f79f43 / prime-control-repeat | minrank | 0.973449 |
| 5943f8f79f43 / prime-control-repeat | dense-quadratic | 0.914331 |
| ddde8c89c095 / f2-false | cyclic | 1.019161 |
| ddde8c89c095 / f2-false | kat | 0.776376 |
| ddde8c89c095 / f2-false | eco | 1.009530 |
| ddde8c89c095 / f2-false | noon | 1.101378 |
| ddde8c89c095 / f2-false | reimer | 1.059597 |
| ddde8c89c095 / f2-false | minrank | 0.952366 |
| ddde8c89c095 / f2-false | dense-quadratic | 1.029021 |
| ddde8c89c095 / f2-false | mq | 0.987586 |
| ddde8c89c095 / f2-false-repeat | cyclic | 0.985623 |
| ddde8c89c095 / f2-false-repeat | kat | 1.059109 |
| ddde8c89c095 / f2-false-repeat | eco | 0.976044 |
| ddde8c89c095 / f2-false-repeat | noon | 1.054611 |
| ddde8c89c095 / f2-false-repeat | reimer | 1.076303 |
| ddde8c89c095 / f2-false-repeat | minrank | 1.003025 |
| ddde8c89c095 / f2-false-repeat | dense-quadratic | 0.992745 |
| ddde8c89c095 / f2-false-repeat | mq | 0.970379 |
| ddde8c89c095 / prime-control | cyclic | 0.978759 |
| ddde8c89c095 / prime-control | kat | 0.997838 |
| ddde8c89c095 / prime-control | eco | 0.996842 |
| ddde8c89c095 / prime-control | noon | 0.978082 |
| ddde8c89c095 / prime-control | reimer | 0.984388 |
| ddde8c89c095 / prime-control | minrank | 0.943138 |
| ddde8c89c095 / prime-control | dense-quadratic | 1.019682 |
| ddde8c89c095 / prime-control-repeat | cyclic | 0.960171 |
| ddde8c89c095 / prime-control-repeat | kat | 0.988294 |
| ddde8c89c095 / prime-control-repeat | eco | 0.997434 |
| ddde8c89c095 / prime-control-repeat | noon | 0.954857 |
| ddde8c89c095 / prime-control-repeat | reimer | 0.962169 |
| ddde8c89c095 / prime-control-repeat | minrank | 1.054192 |
| ddde8c89c095 / prime-control-repeat | dense-quadratic | 0.957128 |

All full-system pairs return equal complete reduced bases with no failures or timeouts. These are development inputs: fourteen systems in seven families over 32003 and 2147483647, plus ten F2 systems in eight families. F2 inputs include ordinary polynomial squares, degenerations and three seeded quadratic systems. The comparator receives canonical generators of the same ideals. This is not the fixed balanced acceptance suite or a held-out evaluation.

| Source | Kernel | B/A | Pair range | Matched below-signal-floor flags |
|---|---|---:|---:|---:|
| 5943f8f79f43 | monomialProducts | 1.053908 | 1.011864–1.461104 | 1 |
| 5943f8f79f43 | productWide | 1.013873 | 1.008303–1.042952 | 3 |
| 5943f8f79f43 | productMisses | 0.281196 | 0.276013–0.285908 | 5 |
| ddde8c89c095 | monomialProducts | 1.001816 | 0.920685–1.019757 | 0 |
| ddde8c89c095 | productWide | 1.007155 | 0.987831–1.013549 | 1 |
| ddde8c89c095 | productMisses | 0.280868 | 0.276911–0.286784 | 0 |

Each kernel experiment retains six fixed trial-major complexity invocations and sixty adjacent matched invocations over sizes 256–4096. Every matched complete-data hash agrees. Matched flags and outliers remain in the aggregates; the complexity runs and their flags are retained separately. The missing-product kernel improves; lookup-only overhead and full-system variability limit the conclusion.

| Source | Comparator suite | Hex/msolve | Equal-family | Pair range | CPU | Peak RSS Hex/msolve KiB |
|---|---|---:|---:|---:|---:|---:|
| 5943f8f79f43 | msolve-f2 | 1.442904 | 1.265655 | 0.644907–2.987789 | 27 | 81992/18004 |
| 5943f8f79f43 | msolve-prime | 1.641843 | 1.641843 | 0.666664–2.538959 | 28 | 79944/20308 |
| ddde8c89c095 | msolve-f2 | 1.799904 | 1.585077 | 0.644238–5.888316 | 50 | 81944/18016 |
| ddde8c89c095 | msolve-prime | 1.708561 | 1.708561 | 0.707834–3.378732 | 64 | 79896/20320 |

| Source / comparator | Family | Hex/msolve |
|---|---|---:|
| 5943f8f79f43 / msolve-f2 | cyclic | 2.769269 |
| 5943f8f79f43 / msolve-f2 | kat | 0.730910 |
| 5943f8f79f43 / msolve-f2 | eco | 2.666611 |
| 5943f8f79f43 / msolve-f2 | noon | 0.682246 |
| 5943f8f79f43 / msolve-f2 | reimer | 0.705306 |
| 5943f8f79f43 / msolve-f2 | minrank | 0.849407 |
| 5943f8f79f43 / msolve-f2 | dense-quadratic | 1.224538 |
| 5943f8f79f43 / msolve-f2 | mq | 2.437396 |
| 5943f8f79f43 / msolve-prime | cyclic | 2.515868 |
| 5943f8f79f43 / msolve-prime | kat | 1.848286 |
| 5943f8f79f43 / msolve-prime | eco | 1.644500 |
| 5943f8f79f43 / msolve-prime | noon | 1.615468 |
| 5943f8f79f43 / msolve-prime | reimer | 1.934573 |
| 5943f8f79f43 / msolve-prime | minrank | 0.969403 |
| 5943f8f79f43 / msolve-prime | dense-quadratic | 1.388173 |
| ddde8c89c095 / msolve-f2 | cyclic | 3.053036 |
| ddde8c89c095 / msolve-f2 | kat | 0.781296 |
| ddde8c89c095 / msolve-f2 | eco | 2.641156 |
| ddde8c89c095 / msolve-f2 | noon | 0.954076 |
| ddde8c89c095 / msolve-f2 | reimer | 0.950938 |
| ddde8c89c095 / msolve-f2 | minrank | 1.135778 |
| ddde8c89c095 / msolve-f2 | dense-quadratic | 2.051112 |
| ddde8c89c095 / msolve-f2 | mq | 2.992570 |
| ddde8c89c095 / msolve-prime | cyclic | 2.852118 |
| ddde8c89c095 / msolve-prime | kat | 2.225317 |
| ddde8c89c095 / msolve-prime | eco | 1.654996 |
| ddde8c89c095 / msolve-prime | noon | 1.612049 |
| ddde8c89c095 / msolve-prime | reimer | 2.015478 |
| ddde8c89c095 / msolve-prime | minrank | 1.003967 |
| ddde8c89c095 / msolve-prime | dense-quadratic | 1.240454 |

msolve commit `3672113ee2c696a2ac9c637636e0f7214f500ba1` uses Clang 23.1.3, `-O3 -march=native`, and `-g 2 -l 2 -t 1`. Compiler and tuning differences are part of the observed gap. Hex remains behind msolve overall on these inputs. No fastest-open-source milestone or language-impossibility claim follows. Candidate production, certificate generation, independent native verification and kernel checking remain separate; only candidate/process performance is timed here.

Both source versions pass all twelve Clang 23.1.3/GCC 16.2.0 ASan+UBSan variants and all nine project gates. Independent oracles compare 567 unique reduced bases with both SymPy and Singular. Revised tests construct RC=1 tables directly, compare all output arenas, cover spare-capacity growth, every borrowed arena alias, marked-linear buffers, intra-table aliases and malformed forward/cyclic links. The `compute-reference` executable uses full initialization of the same native arithmetic; it is not a portable-arithmetic timing.

Runtime `5943f8f79f43`; checks `7cc6296af1b8`. `f4-monomial-batches-initial-5943f8f79f43.tar.xz`: SHA-256 `eb418bb63572d823b98d1fe276557bc59bb2b1a94e164d05c1ee73cc161ab3e8`.
Runtime `ddde8c89c095`; checks `ffc4836b7d74`. `f4-monomial-batches-ddde8c89c095.tar.xz`: SHA-256 `576afda14cf8582687805439fe9346593fa9dc331459c7343f4620ebec974d85`.

Regenerate with `python3 scripts/bench/groebner_batch_report.py --initial reports/bench-results/raw/f4-monomial-batches-initial-5943f8f79f43.tar.xz --capsule reports/bench-results/raw/f4-monomial-batches-ddde8c89c095.tar.xz --report reports/bench-results/hexgroebner-monomial-batches.md --check`. Add `--current` to bind the checkout.
