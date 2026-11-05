# Sparse matrix buffers: measured snapshot

Measured runtime `45745225e6b0` is compared directly with `5fd07b982681`. Current source `8dd7b08ebf35` reproduces the computation, full-initialization and benchmark executables byte for byte; source differences are a checked cost-model comment and exact pinned upstream Lake registrations for unrelated HexRCF targets. The native F₂ scan resolves its stable private buffers once, and loads packed UInt32 indices with unaligned-safe native loads only on known little-endian hosts. Other hosts retain bytewise decoding. Mathematical results, row order, labels, budgets and all eight logical counters are preserved.

All 128 processes and 64 adjacent AB/BA pairs have identical complete outputs and counters. The fixed sweep covers the first size of ten primary families over F₂, F₃₂₀₀₃ and F₂₁₄₇₄₈₃₆₄₇, plus Eco-14/Eco-15 over F₂. Runs use one leased CPU, one thread, degree scheduling, batch size 1024, binary pivots and delayed reduction enabled, and dense pivots disabled.

| Field | Candidate B/A | Process B/A | Candidate pair range | Peak RSS A/B, KiB |
|---|---:|---:|---:|---:|
| 2 | 0.9682 | 0.9733 | 0.7646–1.0531 | 34808/35184 |
| 32003 | 0.9992 | 0.9918 | 0.9103–1.0572 | 515556/530836 |
| 2147483647 | 0.9994 | 0.9965 | 0.9590–1.1950 | 603704/605252 |

| F₂ case | Candidate B/A | Pair ratios |
|---|---:|---|
| eco14-2 | 0.6659 | 0.6743, 0.6576 |
| eco15-2 | 0.6728 | 0.7076, 0.6396 |

These are descriptive point estimates. Every completed observation, outlier and failure is retained; ratios from preliminary optimization stages are not multiplied. Host activity is recorded on the shared AMD EPYC 9455. Production native code uses Clang 21.1.8 and generated C uses SDK Clang 23.1.0 with Lean 4.35.0-rc3. Both builds disable the opt-in AVX-512 route; existing exact AVX2 dispatch remains available. Limits are 300 seconds, 8 GiB address space and 256 MiB per output file, with explicit fixed-corpus parent allowances. The measurements do not establish default-budget admission or complete balanced/parallel acceptance.

All nine project gates and 36 strict Clang/GCC ASan/UBSan configurations are source-bound, including regular, forced-sparse and packed-only profiles. Compiler families, actual Lake compiler/flag declarations, generated driver templates, source manifests and all complete functional outputs are replayed. Native and portable wide-sparse kernels are registered with lean-bench using the O(C+n²) operation model, C=131073, eight targets and complete output/counter consumption. All 85 frozen benchmark verifications pass.

Production capsule SHA-256: `b10736f32f83593bdc95ede90bf6deb1b52425ef2fc60083f2acb62a91eac98b`. Candidate production, certificate generation, independent native certification and kernel checking remain separate costs. Ordinary F₂ polynomial exponents retain their usual meaning; x and x² are distinct.


| Kernel campaign | Function | Verdict | Flagged samples |
|---|---|---|---:|
| first | sparseBinary | inconclusive | 8/18 |
| first | sparseBinaryReference | inconclusive | 7/9 |
| longer | sparseBinary | inconclusive | 2/18 |
| longer | sparseBinaryReference | inconclusive | 0/9 |

Both ordinary complexity campaigns are retained, including the sole longer-batch repeat and all signal-floor flags. Their verdicts are inconclusive; no empirical complexity acceptance or matched implementation speed ratio is inferred.

| Held-out family | Hex/msolve process ratio |
|---|---:|
| dense-quadratic | 1.0065 |
| sparse-structured | 1.1979 |
| positive-dimensional | 1.0606 |

All 27 fixed held-out inputs have 108 successful processes, 54 equal complete bases and no missing/failed observations. The family-balanced process ratio is 1.0854× Hex/msolve. Peak RSS is 1344692/266020 KiB. These observations do not establish a language/runtime limitation.

The comparator is msolve commit 3672113ee2c696a2ac9c637636e0f7214f500ba1, Clang 23.1.3, -O3 -march=native, full reduced output, linear algebra mode 2 and one thread. Full primary solved coverage, equal-thread parallel comparisons, finite-extension coverage, deterministic producer correctness/termination and the fastest-open-source milestone remain required by issue #10987.

Held-out stream SHA-256: `ae5f65b4e34870299f3f908b0a10a6e0e3a22e9c17aa131128a330267b40e30a`. All full bases, fixed inputs, failures, source/executable/compiler identities, raw samples, memory and family ratios are retained and independently replayed. Scientific performance claims never depend on CI timings.
