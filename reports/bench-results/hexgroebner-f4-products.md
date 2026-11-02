# F4 with batched monomial products and strided field products

This source combines [batched existing-product lookup](hexgroebner-product-batches.md)
with [strided Mersenne-prime folding](hexgroebner-matrix-m31-strided.md). The
individual-optimization measurements retain their own source scopes. The
combined observations below come from a separate fresh detached source build;
they are not pooled with those campaigns and do not establish individual
causal contributions by comparing unrelated runs.

Baseline family fingerprint `1e1015abfc77`; candidate `1274c81a9f22`,
commit `003ce2b4d1de8a3ce630cf4582e29bcd21c2b204`, snapshot `2efa46e77ca56257a495f89fe4d902f673a7e254`.
Compute/reference SHA256: `a2a83b62968b4e29b931456057a211c51923d1218d629f77f0f3c2e7511d94c6` /
`fbbcddd1bb06158d4fdc2eadf84812e26778e0c68692a4af349e9a81800f4f0a`. Build/snapshot identifiers may be
capsule-only identifiers after rebasing; exact source overlays and digests remain.

The first adjacent AB/BA campaigns use one algorithm thread, automatically
leased CPUs, grevlex, degree scheduling and primes 32003 and 2147483647.
All 60 complete reduced-basis and algorithm/resource-counter pairs agree,
without failures or timeouts. Every completed sample and outlier remains;
no unchanged repeat was collected. Means weight each pair equally.

| Suite | Pairs | Candidate GM B/A | Median | Range | Process GM B/A |
| --- | ---: | ---: | ---: | ---: | ---: |
| small | 32 | 0.8815 | 0.8874 | 0.7985–1.0381 | 0.9272 |
| medium | 28 | 0.8067 | 0.8008 | 0.7061–0.9479 | 0.8638 |

Candidate time includes normalization, F4 and final interreduction. Process
time includes initialization, parsing and complete output under identical
GNU-time wrappers. Certificate generation, independent final verification
and kernel checking are excluded. These are development-suite observations,
not the SPEC's fixed balanced/held-out leadership acceptance suite. Host
activity, peak RSS, every raw sample and both field-width groups remain in
the capsule without filtering or quiet-host selection.

All nine project checks and eight Clang 23.1.3 / GCC 16.2 ASan/UBSan variants
pass on this combined source. Clang uses seed 0 and GCC seed 1, covering both
forced-collision and ordinary-hash polynomial comparisons and different
coefficients. Each variant additionally runs six adjacent portable/traced
F4 seeds. Exact batch admission, full table bytes, alias snapshots, original
scalar-loop failure prefixes, malformed geometry, arbitrary Nat bounds,
independent M31 arithmetic and vector guard pages are checked. The two CLI
profiles each pass 1134 complete corpus outputs/counters and input/resource
boundaries. ASan is limited by mimalloc; leak checking is disabled.

[Raw capsule](raw/f4-products-1274c81a9f22.tar.gz), SHA256
`b0bd6af2250ebfb200bfea9eb93c82f8e5b958d4bac01f36da62e018901afeb1`; 158 baseline / 159 candidate family
source blobs, 153 verification source blobs and 1004 verified payload digests.
No fastest-open-source milestone or external performance leadership is demonstrated.


Measured Git tree IDs: `HexGroebner` = `7f8da056f783697c4e33d23432bc2393e67b308c`;
`bench/HexGroebner` = `c8216a0a056a318836050319064f36942b7c5abc`.
The [source index](hexgroebner-product-sources.json) records the source-manifest
digest and executable hashes alongside these content-addressed trees. The
combined measured trees equal those at published head `4cfdb89a1c9116181e1ba58003e736e0fae1234a`.

These F4 suites have 2, 4, 5, 6 or 10 variables (small) and 3, 5, 6, 7, 8
or 11 variables (medium). Their gains apply to that measured regime. These
measurements do not cover the adaptive scheduling used at 22 or more variables.
The positive batch counts establish path use and are not an admission rate.
