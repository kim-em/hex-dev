# Short-row matrix primitive kernels

Build commit and snapshot identifiers in these records may be local,
capsule-only identifiers after rebasing; they are not promised to resolve on
GitHub. Each linked capsule retains its exact family source overlay, build
metadata and artifact digests independently of those Git references.

Source fingerprint `d16e17592b4a`, commit `8033b52781065cd37044b4b9c9d0346cfa728ed9`,
snapshot `8b950081de749f61de39185b4f4dd81225f8d4ef`, fresh benchmark SHA256
`81c15f89070a0d50011fabe89e49d807e386440f3b47fb1fda52ee44f3eea249`.
This extends the earlier six-size schedule with rows/buffers of 1, 4 and 16
entries/bytes. Observations remain separate from the earlier source and schedule.

Each operation has one AB/BA whole-sweep campaign (block 0 AB, block 1 BA),
one trial per sweep, nine sizes and 72 completed points total. A is the original
portable operation; B is its bounded native provider with the same Lean model.
Validation uses prime 65537 and dense unit rows prepared outside timing, and
consumes success and every exact prefix counter. Zero-buffer hashing consumes
all bytes. All complete hashes agree. One algorithm thread, automatically
leased CPU 84 on the shared 96-logical-CPU EPYC 9455; loads
24.82/15.49/7.95 → 6.26/13.00/8.87. No host filtering or unchanged repeat.
All samples, RSS, batch lengths, actual repeats, spawn floors and failures remain.

| Operation | Size | Block 0 portable ns | Native ns | B/A | Block 1 portable ns | Native ns | B/A |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| matrixValidate | 1 | 137.21 | 75.78 | 0.5523 | 142.26 | 77.67 | 0.5460 |
| matrixValidate | 4 | 167.01 | 81.98 | 0.4909 | 168.96 | 83.36 | 0.4934 |
| matrixValidate | 16 | 269.98 | 93.16 | 0.3451 | 266.82 | 95.58 | 0.3582 |
| matrixValidate | 64 | 692.62 | 156.89 | 0.2265 | 651.36 | 163.64 | 0.2512 |
| matrixValidate | 256 | 2420.07 | 427.86 | 0.1768 | 2117.62 | 421.57 | 0.1991 |
| matrixValidate | 1024 | 8082.37 | 1415.82 | 0.1752 | 7832.68 | 1418.10 | 0.1810 |
| matrixValidate | 4096 | 31568.10 | 5362.23 | 0.1699 | 30643.04 | 5371.95 | 0.1753 |
| matrixValidate | 16384 | 122572.44 | 21187.68 | 0.1729 | 120866.09 | 21181.68 | 0.1752 |
| matrixValidate | 65536 | 489367.41 | 84673.42 | 0.1730 | 482123.83 | 84051.02 | 0.1743 |
| matrixZeros | 1 | 36.66 | 37.42 | 1.0208 | 36.58 | 37.36 | 1.0215 |
| matrixZeros | 4 | 37.33 | 37.71 | 1.0102 | 40.04 | 37.65 | 0.9405 |
| matrixZeros | 16 | 58.51 | 40.23 | 0.6876 | 58.57 | 40.25 | 0.6872 |
| matrixZeros | 64 | 153.26 | 42.35 | 0.2763 | 156.17 | 42.43 | 0.2717 |
| matrixZeros | 256 | 478.07 | 63.62 | 0.1331 | 479.48 | 63.36 | 0.1322 |
| matrixZeros | 1024 | 1807.76 | 158.24 | 0.0875 | 1801.11 | 158.34 | 0.0879 |
| matrixZeros | 4096 | 7058.61 | 548.71 | 0.0777 | 7050.87 | 537.69 | 0.0763 |
| matrixZeros | 16384 | 28056.78 | 1976.73 | 0.0705 | 28510.91 | 1976.75 | 0.0693 |
| matrixZeros | 65536 | 112140.61 | 7800.61 | 0.0696 | 112295.61 | 7807.64 | 0.0695 |

The native validator is faster even at one entry in both blocks. Fixed call
cost is visible at small sizes; these data do not justify a short-row bypass.
The nine-size normalized-slope fits include that fixed-cost region, so native
fits are inconclusive against the declared linear model. Finite fits do not
prove or refute asymptotic complexity.

| Operation | Block | Arm | Verdict | Normalized slope |
| --- | ---: | --- | --- | ---: |
| matrixValidate | 0 | A | consistent_with_declared_complexity | -0.087293 |
| matrixValidate | 0 | B | inconclusive | -0.155602 |
| matrixValidate | 1 | A | consistent_with_declared_complexity | -0.082419 |
| matrixValidate | 1 | B | inconclusive | -0.159914 |
| matrixZeros | 0 | A | consistent_with_declared_complexity | -0.078048 |
| matrixZeros | 0 | B | inconclusive | -0.339378 |
| matrixZeros | 1 | A | consistent_with_declared_complexity | -0.078261 |
| matrixZeros | 1 | B | inconclusive | -0.339856 |

0 points are below the configured signal floor. This is operation timing,
not certificate generation, independent native verification or kernel checking.
The full-system observations remain in [the separate report](hexgroebner-matrix-primitives-portable.md);
no external leadership claim follows.

[Raw capsule](raw/matrix-primitives-short-d16e17592b4a.tar.gz), SHA256
`2f6fbce031bf8a2976f93b79377e004886f2130f3b4748dc9e24620d1be9c37b`; 158 verified source blobs and 185 verified payload digests.
