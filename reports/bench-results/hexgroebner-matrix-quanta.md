# Larger native scan/gather batches

Increasing ordinary and traced scan/gather batches from 4096 to 65536 transitions does not establish a consistent full-system gain. Keep the existing batch size. Whole-matrix admission and its internal 4096-transition calls are unchanged.

Source `95eb43813565` has compute SHA256 `8313b10346ba82050ffccb83215ac7b82d1c64d7d5d4758d5f253fe2e3f68502`; baseline `e878b78cf727` has `fb6a033166de667e753df9ba554203503bb7bb9e89ad893f351f18f064eb2a1d`. Both fresh detached builds use the archived restored SDK Clang/LLD 23.1.0 wrapper; native FFI uses Clang 23.1.3. These observations are separate from original SDK-wrapper builds.

All measurements are manual on the shared EPYC 9455 host with one requested algorithm thread and an automatically leased CPU. Each input runs adjacent AB/BA. Retain the first campaign and sole unchanged repeat for each observation, all outliers and failures, with no activity filters. These are development inputs, not held-out SPEC acceptance.

| Suite | Campaign | CPU | Candidate B/A | Process B/A |
| --- | --- | ---: | ---: | ---: |
| small | first | 68 | 0.9885 | 0.9574 |
| small | repeat | 16 | 0.9404 | 1.0222 |
| medium | first | 41 | 1.0030 | 0.9809 |
| medium | repeat | 44 | 0.8772 | 0.9176 |

All 240 CLI processes succeed; 120 complete basis pairs and all algorithm counters agree. Small/medium pooled candidate ratios are 0.9642/0.9380, process ratios 0.9892/0.9487, and equal-family process ratios 1.0219/0.9487. The first and repeat campaigns differ materially. Candidate ratios span 0.3224–2.9414 on small and 0.1536–5.7022 on medium. There are zero measured failures or timeouts.

| Fixed campaign | CPU | Case | B/A mean | Candidate median | Range |
| --- | ---: | --- | ---: | ---: | --- |
| first | 1 | cyclic4 | 0.8160 | 1.0010 | 0.1635–1.7834 |
| first | 1 | cyclic5 | 0.6416 | 1.0085 | 0.0317–12.2793 |
| first | 1 | cyclic6 | 0.5436 | 0.7587 | 0.0689–1.4858 |
| first | 1 | katsura3 | 0.9857 | 0.9874 | 0.9613–1.0070 |
| first | 1 | reimer5 | 1.3452 | 1.0913 | 0.2821–3.6662 |
| first | 1 | cyclic6Small | 0.6820 | 0.9568 | 0.2358–1.1760 |
| repeat | 70 | cyclic4 | 1.0105 | 1.0150 | 0.9592–1.0411 |
| repeat | 70 | cyclic5 | 0.5936 | 0.9372 | 0.0564–1.1309 |
| repeat | 70 | cyclic6 | 0.8946 | 1.0057 | 0.2138–4.4715 |
| repeat | 70 | katsura3 | 1.0169 | 1.0158 | 0.9948–1.0429 |
| repeat | 70 | reimer5 | 1.4789 | 1.0286 | 0.7374–4.3443 |
| repeat | 70 | cyclic6Small | 1.1100 | 1.0697 | 0.2317–4.5044 |

All 240 fixed points succeed with equal complete structural output hashes. Fixed Reimer5 regresses in both campaigns; several other cases have extreme variability and inconsistent mean/median evidence. No further unchanged repeat is used. The raw records retain CPU, host load, child RSS, full source/build identities, all samples and commands. The fixed-run contract prose truncates the baseline compute hash; the archived baseline manifest and this report give its complete identity. No uniform speedup claim is supported.

Validation passes the library/theory and conformance build, independent matrix/basis/division oracles, both 1134-output CLI corpora, 32 benchmark checks and every project audit. Four Clang and four GCC ASan/UBSan variants pass. Direct tests exercise 5000 reductions/events/entries, a pending 5000-entry row, every coefficient width, quantum boundaries 4096/4097/65535/65536/65537 and separate work, trace, output-entry and packed-byte exhaustion prefixes. The initial model-build command ran in the parent worktree; the corrected build and an updated malformed-quantum guard pass. Retained logs distinguish these development attempts.

Candidate production includes packing, F4 and final interreduction. Process time also includes initialization, parsing and output. Certificate production, independent certification and kernel replay are excluded. This experiment does not establish the fastest-open-source milestone or a language/runtime impossibility.

- [matrix-quanta-95eb43813565.tar.gz](raw/matrix-quanta-95eb43813565.tar.gz): `2fec699963cfade49e4af958999be4624dc7ed4c0a71db985eda5e711f0d07c1`.
