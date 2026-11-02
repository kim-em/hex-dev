# Bounded validation and zero-buffer primitives

The existing elimination loop uses bounded native row validation and zeroed-buffer allocation through wrappers proved equal to their original Lean models. This changes operations within the existing reference loop; it does not select the separate matrix continuation. The validation call admits at most 65,536 columns and columns+1 entries, with counters at most 2^62−1 and arbitrary Nat error indices/limits. A declined call does no charged work and uses the original validator. Zero-buffer allocation admits at most one MiB; larger buffers use the original implementation.

Full-system sources are baseline `bf218f1c520b` (snapshot `11a177af97ed8a2e142588ccd8d6498f2f002265`) and candidate `e096f91a0bf1` (snapshot `20f995d9b00ea451fe1fb3fb851f1819d7b63c34`). The base is merged main `68c7223028495696762ad3a91c4f6f623acf7902`, with exact family overlays in the capsule. Fresh compute SHA256: baseline `0ff6b19199681cf4d6f375992b665c338a391b5f8ef95d4771c2f76d735bfe34`, candidate `18af17a38e71e429a3a1dd399ed450eadf67d3186afd04ef4be2abdc83d793a4`. Candidate reference-driver SHA256: `4785cc78d474afd153a0033ce3c6fd0d0b596dbae4e95efdfc932852c15d9a88`.

Each suite has one matched AB/BA campaign (block 0 AB, block 1 BA), with one requested algorithm thread and automatically leased CPU. The fixed inputs use grevlex over primes 32003 and 2147483647, and the default scheduling policy. All sixty pairs (120 processes) have equal complete reduced bases and every algorithm/resource counter, including work and allocatedBytes. No failures, timeouts, host-activity filtering or unchanged repeat. Candidate time is the driver’s F4 timer; process time includes parsing/startup/output. Certificate generation, independent verification and kernel checking are separate and excluded from those candidate timings.

| Suite | Pairs | Candidate GM B/A | Median | Range | Process GM B/A | Family-balanced process GM |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| small | 32 | 1.0095 | 0.9993 | 0.8746–1.2009 | 0.9828 | 0.9834 |
| medium | 28 | 0.9745 | 0.9715 | 0.9315–1.0362 | 0.9744 | 0.9744 |

| Suite/family | Candidate GM B/A | Process GM B/A |
| --- | ---: | ---: |
| small/cyclic | 1.0011 | 0.9788 |
| small/dense-quadratic | 1.0386 | 0.9904 |
| small/eco | 0.9678 | 0.9711 |
| small/kat | 1.0127 | 0.9935 |
| small/minrank | 1.0556 | 0.9835 |
| small/noon | 1.0130 | 0.9833 |
| small/reimer | 0.9885 | 0.9833 |
| medium/cyclic | 0.9748 | 0.9749 |
| medium/dense-quadratic | 1.0088 | 1.0071 |
| medium/eco | 0.9620 | 0.9636 |
| medium/kat | 0.9622 | 0.9663 |
| medium/minrank | 0.9971 | 0.9877 |
| medium/noon | 0.9827 | 0.9821 |
| medium/reimer | 0.9356 | 0.9405 |

The small-suite candidate GM regresses about 0.9%; the medium-suite GM improves about 2.6%. This is a modest, mixed full-system result, not a broad speedup or external leadership claim. Small-suite CPU 64 has loads 7.65/5.98/15.80 → 7.36/5.94/15.73; medium-suite CPU 6 has 7.36/5.94/15.73 → 6.68/5.86/15.55. The shared EPYC 9455 host has 96 logical CPUs. All completed samples, process RSS, full inputs/outputs and raw variability remain.

Direct kernels bind source `600ccbc2016f`, snapshot `2236c4c9cbb7d2b68277ab2c8c3b3be9e9340336`, and fresh benchmark SHA256 `a7d1d8ca335a0dbe33badc41c36c4050d355ecb486cf0882779d41411530ab19`. Its F4 driver ELFs are byte-identical to the full-system candidate above; the kernel source and observations remain separate. Both arms use the same benchmark ELF. Prepared valid dense unit rows over prime 65537 are excluded from validation timing; success and every exact charged counter are consumed. Zeroing consumes all bytes through ByteArray hashing, without conversion to boxed arrays. Build-time checks require complete successful equality at every timed size.

Each operation has a first six-size AB/BA whole-sweep campaign (block 0 AB, block 1 BA), one trial per sweep: forty-eight total completed points. CPU 38, one algorithm thread, loads [4.0283203125, 3.73193359375, 10.1767578125] → [1.51904296875, 2.8095703125, 8.77587890625]. The inner target is four seconds and cap thirty-two seconds; actual repeat counts, batch durations, effective targets and spawn floors remain in exports. No sample filtering or unchanged repeat.

| Operation | Block | Size | Portable µs | Native µs | B/A | Portable RSS KiB | Native RSS KiB | Below floor A/B |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| matrixValidate | 0 | 64 | 0.646 | 0.154 | 0.2378 | 68288 | 68424 | False/False |
| matrixValidate | 0 | 256 | 2.087 | 0.415 | 0.1988 | 68296 | 68424 | False/False |
| matrixValidate | 0 | 1024 | 7.751 | 1.394 | 0.1798 | 68288 | 68360 | False/False |
| matrixValidate | 0 | 4096 | 30.686 | 5.306 | 0.1729 | 68300 | 68428 | False/False |
| matrixValidate | 0 | 16384 | 120.536 | 20.952 | 0.1738 | 70344 | 70472 | False/False |
| matrixValidate | 0 | 65536 | 480.565 | 83.496 | 0.1737 | 74444 | 74508 | False/False |
| matrixValidate | 1 | 64 | 0.640 | 0.154 | 0.2401 | 68360 | 62268 | False/False |
| matrixValidate | 1 | 256 | 2.088 | 0.420 | 0.2010 | 68360 | 68364 | False/False |
| matrixValidate | 1 | 1024 | 7.734 | 1.390 | 0.1797 | 68360 | 68360 | False/False |
| matrixValidate | 1 | 4096 | 30.370 | 5.316 | 0.1751 | 68364 | 68364 | False/False |
| matrixValidate | 1 | 16384 | 120.599 | 20.964 | 0.1738 | 70412 | 70408 | False/False |
| matrixValidate | 1 | 65536 | 480.251 | 83.111 | 0.1731 | 74504 | 74508 | False/False |
| matrixZeros | 0 | 64 | 0.150 | 0.042 | 0.2815 | 68360 | 68360 | False/False |
| matrixZeros | 0 | 256 | 0.479 | 0.063 | 0.1324 | 68364 | 68364 | False/False |
| matrixZeros | 0 | 1024 | 1.802 | 0.159 | 0.0882 | 68360 | 68360 | False/False |
| matrixZeros | 0 | 4096 | 7.038 | 0.543 | 0.0771 | 68376 | 68360 | False/False |
| matrixZeros | 0 | 16384 | 28.012 | 1.981 | 0.0707 | 68436 | 68360 | False/False |
| matrixZeros | 0 | 65536 | 111.918 | 7.801 | 0.0697 | 68436 | 68360 | False/False |
| matrixZeros | 1 | 64 | 0.156 | 0.042 | 0.2712 | 68436 | 68360 | False/False |
| matrixZeros | 1 | 256 | 0.477 | 0.063 | 0.1327 | 68360 | 68360 | False/False |
| matrixZeros | 1 | 1024 | 1.804 | 0.159 | 0.0880 | 68360 | 68360 | False/False |
| matrixZeros | 1 | 4096 | 7.042 | 0.540 | 0.0767 | 68436 | 68360 | False/False |
| matrixZeros | 1 | 16384 | 27.999 | 1.976 | 0.0706 | 68372 | 68496 | False/False |
| matrixZeros | 1 | 65536 | 111.885 | 7.817 | 0.0699 | 68436 | 68360 | False/False |

All complete output hashes agree; 0 points are flagged below the signal floor. RSS includes the Lean runtime baseline. The normalized slope fits log(time/n) against log(n), with zero corresponding to the declared linear model. Finite fits are not asymptotic proofs.

| Operation | Block | Arm | Verdict | Slope |
| --- | ---: | --- | --- | ---: |
| matrixValidate | 0 | A | consistent_with_declared_complexity | -0.017339 |
| matrixValidate | 0 | B | consistent_with_declared_complexity | -0.039199 |
| matrixValidate | 1 | A | consistent_with_declared_complexity | -0.017333 |
| matrixValidate | 1 | B | consistent_with_declared_complexity | -0.041339 |
| matrixZeros | 0 | A | consistent_with_declared_complexity | -0.015208 |
| matrixZeros | 0 | B | consistent_with_declared_complexity | -0.123632 |
| matrixZeros | 1 | A | consistent_with_declared_complexity | -0.014776 |
| matrixZeros | 1 | B | consistent_with_declared_complexity | -0.123198 |

The direct primitive gains are substantially larger than the full-system gain. These data do not establish a cause for the remaining F4 gap, and no current external comparator sweep is included. The fastest-open-source milestone remains open.

All nine local project checks pass for the full-system candidate, including independent oracles, both 1,134-case drivers and 39 benchmarks. Four additional registered kernels subsequently pass all 43 benchmark verifications and phase checks. Eight Clang/GCC ASan/UBSan variants pass for primitive commit `6dc55d5642`; after rebasing through the shared inline validateRows function, complete conformance and full checks pass again. The native C primitive source is unchanged across that refactor. Each sanitizer variant records 198,740 native row-validation calls and 42,426 zero-buffer calls; direct admission/result comparisons prevent silent fallback on admitted cases. Tests include malformed rows, arbitrary Nat indices/limits, scalar counter boundaries, zero/allocation caps and complete immutable input/prefix comparisons. ASan coverage is limited by mimalloc and leak detection is disabled.

[Raw capsule](raw/matrix-primitives-e096f91a0bf1.tar.gz), SHA256 `1bf31e31cea8f399e5222aca24d90d92398cc30fd2a4273e727038b09ea6ac4a`; 157 baseline, 157 full-system and 158 kernel Git source blobs; 1005 payload digests verified after packing. The analysis file describes one campaign per suite, not pooled data across sources.

One diagnostic repeat of the small suite uses source `600ccbc2016f` and its
verified byte-identical F4 drivers, with the same baseline. The source snapshot
and observations are separate from the first campaign and are not pooled.
All 32 pairs (64 processes) have equal complete bases and every counter.
Candidate GM B/A is 0.9881, median
0.9917, range 0.9467–1.0235; process GM is
0.9706, family-balanced process GM 0.9710. The first
campaign's 1.0095 and repeat's 0.9881 leave the small candidate-time effect
near neutral. This is the single allowed unchanged diagnostic repeat; no
further repeat is used. CPU 76 loads are 0.63/1.44/6.70 at start and end.

[Repeat capsule](raw/matrix-primitives-small-repeat-600ccbc2016f.tar.gz), SHA256
`0ac06e034f691777410d29045828b5c535d3eb3c0a95cd29f89808361a8120c7`;
230 verified payload digests. It retains all observations, inputs, full
outputs, RSS and metadata; exact source blobs remain in the main capsule.
