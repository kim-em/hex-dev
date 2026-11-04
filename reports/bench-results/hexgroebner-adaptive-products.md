# Adaptive monomial products: admission and discarded work

Polynomial multiplication limits slices to
`max(1,min(64,floor(4096/(3*arity+4))))`, leaving headroom for extra hash-chain
headers. A one-term slice retains the original scalar loop (arity 682 and
above). The native provider rejects impossible full slices in O(1), using the
minimum successful cost `3*arity+1` before reading exponents. Complete success
or unchanged-table deferral remains the result contract. Scalar failure
prefixes are compared against the original loop; `productsWith_spec` proves
the pure batch wrapper equal to its reference, rather than a theorem for the
complete polynomial loop or C machine code.

Native diagnostics separately count accepted batches/terms, deferred calls
and discarded visit reservations. Reservations conservatively count the full
preparation/comparison allowance, including early failures; they are not CPU
cycles and do not change the algorithm's resource counters. Every deferred
attempt stays within 4096 reservation units. No admission rate is inferred
from the intentionally exhausted conformance corpus.

The final fresh executable source is `5166fcd8b3df`, commit
`d0b968945ff4371346dda8fb7e591cfb25b97a88`, snapshot `9aae96875f849fb5f8aa49e9ccb621c11a8a0f6b`.
Compute/reference SHA256: `ac6068db5657d72677caa604daae0fb1ead9d3e7de2d36df5f5e81537b6ec32e` /
`77c765aadbfe835619a0b916cd754cd5e5b54b9995f168ef794ce3a6cb9b321e`. Its `HexGroebner` tree is
`35a16e0c7cb187ad9f1b7fd3086fa955889f5f37` and `bench/HexGroebner` tree is
`03bf6734e75c27cbfe0429747dea21ebc012fd03`. The current verification head `b2dc5953f27a0077d0dcf7e73cf01a7312eddd97` has
those exact trees. Local commit IDs may become capsule-only after squash or
rebase; the content-addressed trees and complete source overlays remain.

The two source campaigns below are separate first adjacent AB/BA observations,
not pooled. One algorithm thread, automatic CPU lease, grevlex, degree
scheduling, primes 32003 and 2147483647. Every complete basis and resource
counter agrees in all 120 pairs across the two campaigns. All completed
samples/outliers remain, without filtering or unchanged repeat. Means weight
each pair equally. Inputs have 2/4/5/6/10 variables (small) and 3/5/6/7/8/11
(medium); these are development suites, not the fixed balanced/held-out
leadership acceptance suite.

| Source | Suite | Pairs | Candidate GM B/A | Median | Range | Process GM B/A |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| 88dc2e32d9ca | small | 32 | 0.8902 | 0.8787 | 0.7941–1.0672 | 0.9599 |
| 88dc2e32d9ca | medium | 28 | 0.8153 | 0.8221 | 0.7104–0.9538 | 0.8774 |
| 5166fcd8b3df | small | 32 | 0.8975 | 0.8746 | 0.8002–1.4171 | 0.9325 |
| 5166fcd8b3df | medium | 28 | 0.8236 | 0.8126 | 0.7083–0.9499 | 0.8653 |

Candidate time includes normalization, F4 and final interreduction. Process
time also includes initialization, parsing and full output under identical
GNU-time wrappers. Certification, independent verification and kernel checking
are excluded. Peak RSS, host activity and all raw samples remain available.

The source88dc2e32d9ca microbenchmarks compare scalar per-term native operations
(A) and batch-native operations (B) in one fresh executable. Preparation is
excluded; support assembly, independent ID validation and complete output
support/final-workspace/count/work consumption are included. The miss benchmark
also consumes every changed arena, metadata and index byte. Each complete
64-term slice misses only its last product, so its first 63 hits are discarded
and replayed. The wide benchmark uses 22 variables and 58-term slices. The
Monomial and native-provider files are byte-identical to the final source;
the benchmark file's later change only fixes a bare cost-model comment.

| Case | Products | Block 0 B/A | Block 1 B/A |
| --- | ---: | ---: | ---: |
| hits | 256 | 0.2242 | 0.2233 |
| hits | 512 | 0.2239 | 0.2230 |
| hits | 1024 | 0.2246 | 0.2270 |
| hits | 2048 | 0.2277 | 0.2361 |
| hits | 4096 | 0.2316 | 0.2278 |
| misses | 256 | 1.1490 | 1.1598 |
| misses | 512 | 1.1584 | 1.1807 |
| misses | 1024 | 1.1660 | 1.1561 |
| misses | 2048 | 1.1632 | 1.1512 |
| misses | 4096 | 1.1311 | 1.1676 |
| wide | 256 | 0.3833 | 0.3900 |
| wide | 512 | 0.3842 | 0.3784 |
| wide | 1024 | 0.3841 | 0.3821 |
| wide | 2048 | 0.3838 | 0.3787 |
| wide | 4096 | 0.3814 | 0.3787 |

All 60 complete microbenchmark output hashes agree. Last-term misses regress
about 13–18%; this cost is retained explicitly. Existing-product and wide
lookup gains do not imply a gain for arbitrary insertion-heavy workloads.
Partial-prefix reuse remains a possible optimization; this implementation
keeps the current contract with bounded, measured discarded work.

The untimed diagnostic runs each unique suite input once through normal and
link-wrapped source88dc drivers. All 30 complete output/metadata/resource
comparisons agree after removing only `candidateNanos`. Counts are for complete
candidate production, including normalization, symbolic work and final
interreduction. They are not timings or a family-balanced performance metric.

| Suite | Accepted | Deferred | Admission | Accepted terms | Discarded reservations | Maximum per deferral |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| small | 21822 | 2234 | 90.71% | 859226 | 690140 | 1956 |
| medium | 120800 | 7750 | 93.97% | 5850532 | 2345560 | 2183 |

All nine final project checks and eight Clang23.1.3/GCC16.2 ASan/UBSan variants
pass. Native/model attempts must accept deterministic newest-chain-head
fixtures at the calculated cap for arities21/22/65/1365 and defer above it.
The compiled 22-variable multiplication must accept multi-term batches for all
128 terms with zero deferrals. The runtime-seeded last-term-miss window must
increase both deferrals and discarded reservations. The portable public F4
window checks zero accepted AND deferred provider calls. Scalar-loop boundary
comparisons cover681/682/1365/1366 variables. Complete failure tables/counters,
alias snapshots, malformed geometry, arbitrary Nat bounds, independent field
arithmetic, vector guard pages and kernel axiom audits remain covered. ASan is
limited by mimalloc; leaks are disabled. Failed cost-comment and precomputed
fixture probes are retained with their corrected checks.

Final F4 counter windows (which deliberately include exhausted calls):

| Compiler/seed | Accepted batches | Terms | Deferred batches | Discarded reservations |
| --- | ---: | ---: | ---: | ---: |
| clang/0 | 4692 | 11786 | 29075 | 486291 |
| gcc/1 | 4692 | 11786 | 29075 | 486291 |

Each compiler row agrees across its four build variants. These conformance
windows establish coverage and bounded waste, not normal-workload hit rates.

[Raw capsule](raw/f4-product-admission-5166fcd8b3df.tar.gz), SHA256
`ad3c8f3c48d4a06b7319af1b71fa881ca12755dcd6db4bfb4f8418bc8f8ebdf8`; 158 baseline / 159 adaptive /
159 final family source blobs, 153 final verification source blobs
and 1872 verified payload digests. No fastest-open-source milestone or
external performance leadership is demonstrated.
