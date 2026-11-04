# Groebner native compiler selection

The optional `hexGroebnerCC` Lake setting selects the compiler for the five Groebner native objects. The default remains `cc`; other libraries and Lean-generated C retain their existing compiler choices. The compiler path string and flags participate in each object’s build trace. The executable’s contents and PATH resolution are not part of that trace; use an absolute immutable compiler path for reproducible builds and clean native objects after replacing a compiler in place.

Use `lake -R -KhexGroebnerCC=/absolute/path/to/clang build HexGroebner` and restore defaults with `lake -R build`. Lake retains configured options across later plain builds; reconfiguration resets other `-K` settings, which must be supplied again when needed. The freeze tool makes compiler commands absolute while preserving symlink invocation names, and records compiler versions, executable hashes, build options and supplied wrapper/config inputs.

## Scoped compiler comparison

Host `chungus2`; one algorithm thread and automatically leased CPUs recorded per campaign. Groebner C: clang version 23.1.3; other native sources: clang version 21.1.8; Lean-generated C: clang version 23.1.0 (https://github.com/llvm/llvm-project ea7d852a70e8bdfaf601d6626a760f9771b2c4b4). Both arms use identical inputs, grevlex, degree scheduling and complete unchecked-candidate output. Certificate generation, independent native verification and kernel replay are excluded from timing.

| Kernel | Override/default B/A | Pair range | Signal flags |
|---|---:|---:|---:|
| u16-dense | 1.005718 | 0.946243–1.089667 | 3 |
| u16-strided | 0.931243 | 0.828008–0.994651 | 0 |
| m31-dense | 1.025123 | 0.994801–1.172420 | 4 |
| m31-strided | 0.901907 | 0.750321–0.997646 | 5 |

All 72 kernel invocations (32 matched pairs plus complexity ladders) are retained, with equal complete-output hashes. The fixed trial-major ladders and adjacent AB/BA pairs use one-second batches; preparation is excluded and validation, allocation, elimination, decoding and complete-output hashing are included. Signal flags remain included and limit interpretation. The strided kernels improve with the scoped override, but those gains do not carry over to full F4 candidate time on these inputs.

| Full F4 campaign | Process B/A | Candidate B/A | Process pair range | Peak RSS A/B (KiB) |
|---|---:|---:|---:|---:|
| f4 | 0.992638 | 1.031298 | 0.403054–4.615783 | 70044/71796 |
| f4-repeat | 0.923735 | 1.138220 | 0.233584–3.169040 | 72836/73960 |

Each campaign retains all 56 processes across fourteen inputs from seven families at 32003 and 2147483647. The second is the single unchanged repeat after an inconclusive first campaign. All 112 processes (56 pairs) agree on complete outputs and every non-time counter. There are no failures or timeouts. Candidate time is slower with the Groebner-only override in both campaigns, while the noisy process ratios point the other way. The scoped option shows no candidate-time benefit and does not reproduce the broader compiler experiment’s improvement. Broad pair ranges preclude an overall speedup claim. The compiler control is optional and makes no fastest-open-source claim.

## Broader compiler experiment and remaining gap

A separate source-identical experiment changed host `cc` to Clang 23.1.3 for native objects compiled in fresh project builds, with the SDK compiler fixed and pinned dependency artifacts shared. This is a different comparison from the Groebner-only option above; its samples are not pooled with it.

| Global-compiler campaign | Process B/A | Candidate B/A |
|---|---:|---:|
| f4 | 0.958295 | 0.951034 |
| f4-repeat | 0.957244 | 0.949575 |

That broader build remains 1.912043× slower than msolve in matched process time on this seven-family suite. All 56 processes complete with 28 equal complete-basis pairs. msolve revision `3672113ee2c696a2ac9c637636e0f7214f500ba1` uses Clang 23.1.3, native CPU tuning, deterministic elimination (`-l 2`), full reduced output (`-g 2`) and one thread. This comparator observation is neither the default nor the Groebner-only build; no matched current-msolve gap was collected for either of those builds in these capsules. msolve uses native CPU tuning while this Hex build retains runtime dispatch with AVX-512 off. The comparison does not cover held-out/hard acceptance families and does not establish the full SPEC milestone.

## Verification and provenance

Clang/GCC ASan+UBSan pass twelve opt-in-AVX512/forced-AVX2/scalar and wide-reduction/remainder variants. All nine project checks pass at runtime `a5a3a3acc086`, including the 2,264-job executable/theory build, independent oracles, driver checks, benchmark verification, DAG, phase, release manifest and source checks. The cache test switches default Clang 21 → Clang 23 → unchanged Clang 23 → GCC 16 → default Clang 21. Each changed selection rebuilds all five objects with matching ELF compiler records; the unchanged selection reuses them; restoring the default reproduces the original hashes.

Fresh final-source builds reproduce all measured executable hashes. The default executables match the earlier default baseline byte for byte. The post-measurement source difference only resolves compiler commands before detached builds while preserving symlink invocation names; production algorithms and native C sources are unchanged. A compiler wrapper that rejects its resolved filename passes a fresh detached build when invoked by its alias, reproducing every measured override executable hash. A GCC 16 override builds and links the library and driver through Lake; fourteen untimed driver replays reproduce every complete basis and non-time counter. Restoring defaults reproduces all three default executable hashes. No additional timing samples were collected for that tool fix. Failed SDK-header and concurrent Git-index-lock setup attempts are retained as diagnostics and contribute no timing samples.

Measured override runtime `4abe7f39fd7a`; verified runtime `aaeef06c28e8`, checks `7abfc10437ea`. The capsules retain exact source blobs, source manifests, compiler/wrapper inputs, raw samples, outputs, memory, host activity and verification logs. Collection scripts retain their recorded host paths; rerunning them elsewhere requires adapting those paths.

`f4-native-cc-option-4abe7f39fd7a.tar.xz`: SHA-256 `e56c814a9f9a3e1affb837ccf32b57d7229bf00681de256fd7a1b3a6ce697af6`.
`f4-native-cc-guards-a5a3a3acc086.tar.xz`: SHA-256 `bf3dc9d67f00b7e5b6e5bfb68ae3a3f4b4731b780af57a99611e2c037c2eb7af`.
`f4-native-compiler23-13a33eb6a851.tar.xz`: SHA-256 `401428e3583f5635af25e0996477bf3a383400c951395d7666c82c4a07be4fe8`.
`f4-native-cc-linked-audit-aaeef06c28e8.tar.xz`: SHA-256 `447712b73a22f40dfc1c5d665ff3ff686ff281154c63ae563b78d326f1df7820`.

Regenerate with `python3 scripts/bench/groebner_compiler_report.py --science reports/bench-results/raw/f4-native-cc-option-4abe7f39fd7a.tar.xz --guards reports/bench-results/raw/f4-native-cc-guards-a5a3a3acc086.tar.xz --global-compiler reports/bench-results/raw/f4-native-compiler23-13a33eb6a851.tar.xz --audit reports/bench-results/raw/f4-native-cc-linked-audit-aaeef06c28e8.tar.xz --report reports/bench-results/hexgroebner-compiler.md --check`.

Add `--current` only when checking the measured runtime/check source snapshot.
