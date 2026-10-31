# F4 reducer traversal and budget accounting

The retained implementation inlines `Computation.spend` and caches each
reducer-trie node's path length. Lookup and divisor enumeration therefore keep
only node identifiers on their traversal stacks, avoiding an allocated pair
for every visited edge. Reducer choice, traversal order, exact divisibility,
parent budget charges and exhaustion behavior remain identical.

Four matched observations use Lean `v4.35.0-rc3`, one computational thread on
the shared host, and automatically leased CPUs. Each observation runs adjacent
AB and BA arms for cyclic-5, cyclic-6 and Katsura-3, with three repetitions per
arm and a 0.5-second inner floor. All 144 completed samples are retained.
Every complete structural basis hash agrees. Input generation is excluded;
canonicalization through final interreduction, interchange decoding and hashing
are included. Results are unchecked candidates. No certification or kernel
checking time is included.

The [summary](hexgroebner-allocation-summary.json) gives medians, paired ratios,
hashes and archive digest. The [raw archive](hexgroebner-allocation-samples.tar.gz)
contains every export, log, source manifest, exact measurement script,
compiler/toolchain and binary identity, affinity and host-load metadata. It also
contains each measured `Runtime.lean`, including variants absent from the
retained implementation. No observation is discarded because of host activity.
The native-row baseline is identified by source fingerprint `1c423e2b8a95` in
the [row-update report](hexgroebner-native-rows.md).

| Change in B | A → B source fingerprints | cyclic-5 B/A | cyclic-6 B/A | Katsura-3 B/A |
| --- | --- | ---: | ---: | ---: |
| Inline budget helper | `1c423e2b8a95` → `6a51dd194b2c` | 0.980 | 0.980 | 0.971 |
| Direct record destructuring | `1c423e2b8a95` → `e6054e351047` | 1.007 | 1.000 | 1.004 |
| Explicit record-ownership boundary | `1c423e2b8a95` → `a8ba884e6d94` | 1.011 | 1.004 | 1.018 |
| Cache trie depth; store node IDs alone | `6a51dd194b2c` → `381443babeda` | 0.930 | 0.958 | 0.976 |

Ratios are geometric means of the two within-block median ratios. Inlining
shows a small 2–3% reduction. Record destructuring compiles to the same nested
record copy and has essentially unchanged time. The explicit function boundary
permits reuse of the statistics record but reallocates the outer workspace;
its measured time is slightly worse. Both record rewrites are excluded from
the implementation. Removing traversal pairs shows about 4% and 2% less time on cyclic-6 and
Katsura-3. Cyclic-5 has B/A = 0.891 in AB and 0.970 in BA: its AB baseline
is slower than its BA baseline and than the same binary in the preceding
inlining observation. The 0.930 paired aggregate retains both blocks, but the
size of the cyclic-5 effect is **inconclusive**. The per-block range is about
3–11% less time; no 7% representative improvement is established.

Conformance compares trie results with an exhaustive scan on 400 queries,
including zero variables, duplicate leading monomials, sparse-reducer preference
and exponent-width boundaries through `2^32−1`. Existing work-threshold and
resumption checks still pass. All 567 emitted bases agree between native and
scalar row routes, including cumulative counters, and match both Singular and
SymPy F5B. These small-system measurements identify useful local changes; they
do not demonstrate the balanced-suite performance milestone or a language
barrier.
