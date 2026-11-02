# Sparse validation across the UInt32 column range

The native row validator now admits at most 65,537 entries independently of
ambient column count, up to 2^32−1 columns. This replaces the former
65,536-column cutoff. The uninterruptible work bound remains 65,537 entry
inspections and 524,296 valid payload bytes. Larger rows, counters outside the
admitted range and unsupported platforms use the original Lean validator.
Exact errors, charge order, arbitrary Nat indices/limits and all statistics
remain unchanged. Zero-buffer allocation has its existing one-MiB cap.

Source fingerprint `c15c7075d207`, commit `679a7c0cdbf298d1a64d8c25d508996bdb51cced`,
snapshot `1d6229ed7d98aee2ce5abc7b109f864529322ae1`. Fresh compute SHA256
`2e26e3b4f673c58cf5b5ae32be2f6baf4b686b868b6334f10eb2f51a88f6863b`; reference
`f997ad2eb20fe0d06dbc89a5d1a9e2c5f18f803173a0f3ea804ef1b19db74757`. Fresh benchmark SHA256
`3da74bbf593ca81e9856f1738d2c9b89e2e0d7cae26865abd31d118975a49fd3`. The capsule contains the exact source overlay,
compiler/linker commands, toolchain and build logs.

This first direct AB/BA whole-sweep campaign uses one algorithm thread and
leased CPU 10 on the shared EPYC 9455. Each sweep has one trial at
nine row lengths; 36 completed points total. Prime 65537, ambient column count
2^32−1, prepared valid unit rows excluded from timing. No dense workspace of
that ambient width is allocated: this measures the validator operation.
A is the original portable validator; B is its bounded native provider.
Success and every exact prefix counter are consumed. Complete hashes agree
at every size. All samples, RSS, actual repeats, batch lengths, floor flags,
failures and host context remain. No filtering or unchanged repeat.

| Entries | Block 0 portable ns | Native ns | B/A | Block 1 portable ns | Native ns | B/A |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 208.28 | 84.18 | 0.4041 | 144.37 | 90.12 | 0.6242 |
| 4 | 167.13 | 82.23 | 0.4920 | 167.65 | 80.99 | 0.4831 |
| 16 | 289.38 | 93.64 | 0.3236 | 268.06 | 91.86 | 0.3427 |
| 64 | 666.70 | 149.95 | 0.2249 | 652.48 | 157.13 | 0.2408 |
| 256 | 2378.86 | 414.51 | 0.1742 | 2129.40 | 401.46 | 0.1885 |
| 1024 | 8242.27 | 1354.40 | 0.1643 | 7853.82 | 1347.04 | 0.1715 |
| 4096 | 35782.41 | 5142.31 | 0.1437 | 32385.70 | 5125.05 | 0.1583 |
| 16384 | 130346.99 | 20363.16 | 0.1562 | 122329.21 | 20265.50 | 0.1657 |
| 65536 | 500891.29 | 91610.87 | 0.1829 | 487458.10 | 81610.71 | 0.1674 |

Native validation is faster at every measured length in both blocks. These
operation results do not establish a full F4 improvement. Normalized slope
fits include fixed call cost at small sizes; finite observations do not prove
asymptotic complexity.

| Block | Arm | Verdict | Normalized slope |
| --- | --- | --- | ---: |
| 0 | A | consistent_with_declared_complexity | -0.082053 |
| 0 | B | consistent_with_declared_complexity | -0.149890 |
| 1 | A | consistent_with_declared_complexity | -0.080113 |
| 1 | B | inconclusive | -0.159263 |

0 points are below the configured signal floor. Candidate production,
certificate generation, independent native verification and kernel checking
are not timed here. No external leadership claim follows.

All nine project checks pass, including independent oracles, both 1,134-case
drivers and 45 benchmark verifications. Eight Clang/GCC ASan/UBSan variants
pass; each records 1,771,500 validation and 29,892 zero-buffer calls before
F4 diagnostics. Tests cover the exact 65,537-entry admission boundary and
65,538-entry fallback, high column bits, all coefficient widths, independent
and saturated limits, immutable borrowed records/buffers and public portable
F4 routing. ASan is limited by mimalloc; leak detection is disabled.

[Raw capsule](raw/matrix-wide-validation-c15c7075d207.tar.gz), SHA256
`71a9a0444594ba58575f05a90414c1cd23dd7c2f00fac58ef7211165d3e7fb0d`; 158 source blobs and 206 payload digests verified.
