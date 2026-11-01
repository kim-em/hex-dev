# Bounded packed reducer-trie lookup

Small basis-specific divisibility indices retain a typed, validated packed tree.
The validator admits at most 2048 nodes, 2047 edges and arity 4096. Each nonroot
has exactly one parent and depth increases on every edge; edge spans are exact.
In the measured `3949a0dadd7a` snapshot, leaf records retain the source basis
index, term count and leading monomial. The combined implementation uses
Lean-assigned priorities instead; see [the combined report](hexgroebner-symbolic.md).
The native validator and lookup borrow immutable inputs and keep no pointers.
A fixed 2048-entry stack and at most 4095 charged node/edge visits bound lookup.
All source-array spans are checked before reads. Larger trees, incompatible
arenas and insufficient preparation allowances retain the original traversal.

Selection preserves sparse-row preference, then higher leading degree, then
the existing LIFO traversal tie. Node and edge charges precede each visited
prefix, including exhaustion. Encoding/validation charge the parent work and
packed-byte allowances. Queries receive the current monomial arena and width,
so extension and widening preserve stable identifiers. Pair-divisor enumeration
and the mathematical work performed by F4 remain unchanged.

Measured source snapshot `3949a0dadd7a` identifies both diagnostic campaigns and
fixed benchmarks. Baseline snapshot `802ae51122d7` is the packed-monomial
comparison implementation. The capsule retains exact source blobs, frozen
executable hashes, complete outputs, schedules, host context and raw samples.
Later integration snapshot `9e0ab9d9c2d6` includes the standalone CLI and guard
probes. The validation capsule checks exact Git-blob equality of the measured
`Reducer.lean`, `NativeTrie.lean`, `trie_lookup.h` and `row_update.c`; it does not
relabel the earlier measurements as observations of the later CLI executable.

The shared host is AMD EPYC 9455. Each diagnostic campaign uses 16 development
inputs from seven families, primes 32003 and 2147483647, one algorithm thread
and an automatically leased CPU. Adjacent arms alternate AB then BA. CPU84 and
the single permitted unchanged repeat on CPU92 each retain 64 successful
processes, zero failures/timeouts and 32 agreeing complete reduced-basis pairs.
All completed samples and outliers are included. Only preparation work and
packed allocation counters differ; matrix statistics and bases agree.

Candidate time covers canonical input, F4 and final interreduction. Whole-process
time additionally covers initialization, parsing, full output and identical GNU
time wrappers. Certificate generation, independent certification and kernel
checking are excluded. This comparison uses the historical full-initialization
JSON driver, so process ratios do not predict the standalone CLI's gains.

| Observation | Candidate B/A | Process B/A |
| --- | ---: | ---: |
| CPU84 | 0.9223 | 0.9305 |
| CPU92 | 0.9252 | 0.9950 |
| All 64 pairs | 0.9237 | 0.9622 |
| Pooled median | 0.9281 | 0.9688 |
| Pooled range | 0.6964–1.2656 | 0.4447–2.0623 |

Peak post-exec RSS is baseline/experiment 90152/87488 KiB on CPU84 and
95368/93260 KiB on CPU92. Per-field candidate ratios are 0.9174 at 32003 and
0.9300 at 2147483647. These are all-pair geometric means, not family-balanced
leadership evidence. No held-out or fastest-open-source claim is made.

Registered fixed benchmarks retain 120 points on CPU77 and 120 on CPU64,
using their declared five repetitions and adjacent AB/BA. Complete structural
result hashes agree. All ratios normalize by actual inner repeats.

| Fixed case | Pooled geometric mean | Median | Range |
| --- | ---: | ---: | --- |
| cyclic4 | 1.0137 | 1.0035 | 0.9660–1.2046 |
| cyclic5 | 0.9609 | 0.9835 | 0.7837–1.0685 |
| cyclic6 | 1.0049 | 0.9621 | 0.6610–1.8546 |
| katsura3 | 0.9827 | 0.9774 | 0.9383–1.0477 |
| reimer5 | 0.9398 | 0.9152 | 0.6055–1.5682 |
| cyclic6Small | 1.0043 | 0.9613 | 0.3873–2.1035 |

Independent validation covers the original node traversal and the portable
packed model, all supported exponent widths, arity and node boundaries,
malformed validators/arenas, huge Nat inputs, ties and exact exhaustion prefixes.
Maximum-stack guard-page tests protect both ends of borrowed arrays and make
valid inputs read-only. Four Clang and four GCC ASan/UBSan compiled variants
pass; native counters show 2247 trie calls with two intended malformed-arena
declines, and 485 F4 calls with no decline. The integrated build passes all
1956 relevant conformance/theory targets, both 567-case CLI comparisons,
175 independent matrix oracles, 567 SymPy/Singular reduced-basis oracles,
1288 division cases and the 32-check benchmark verification gate. All 567
fixture changes are restricted to `work`, `serialWork` and `referenceWork`.
Dependency, phase, released-manifest and copyright checks pass.

- [prototype-trie-compare-3949a0dadd7a.tar.gz](raw/prototype-trie-compare-3949a0dadd7a.tar.gz):
  `da343f8e76d17f8688b02b9942c46b43e27d91b40da19aef923f54870df6fcdf`.
- [trie-validation-9e0ab9d9c2d6.tar.gz](raw/trie-validation-9e0ab9d9c2d6.tar.gz):
  `fd854c5b1b2a19d9564967430694bc41f7d58d3f5f9a59d7a895905c7a11db48`.
