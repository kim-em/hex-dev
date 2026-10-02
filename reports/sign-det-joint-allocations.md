# Allocation in joint Thom queries

The existing joint-query family completes and compares the real roots 1 and −1
of Xⁿ−1 and Xⁿ+1. Comparison constructs the common head −(X²ⁿ−1)/2 and checks
both re-encodings; each joint table has 3n+1 ordered queries. Replay checks both
supplied trees. See the [input inventory](sign-det-joint-inputs.md) and
[running-time report](sign-det-joint-performance.md) for the precise operations,
independent root/sign oracle and separate timing evidence.

This collection measures successful allocation requests while each actual
callback executes. Preparation, initialization and the native answer check are
outside the counted interval. The [capture method](sign-det-allocation-method.md)
describes the wrapped allocation entry points, nesting guard, controlled ABI
fixtures, direct-call audit and coverage limitations. The three buckets classify
intercepted entry points; the `lean_alloc_*` bucket is not a count of every Lean
object. GMP reallocation contributes the newly requested size. These are
cumulative requested bytes, not peak live memory or scientific running times.

The [retained records](data/sign-det-allocations/joint-25b179f5c/metadata.json)
identify clean source `25b179f5c8f2143cd77753cd8c802d364aefd958`, its executable,
generated callback ABI, compiler, Valgrind 3.27.1, wrapper sources, allocator
inventory and disassembly audit. All sources and the binary remain unchanged
at the end. On `chungus2`, the driver leased CPU 56 and ran three fixed
trial-major rounds over degrees 3, 7 and 15. At each degree it ran completion,
comparison, reduced replay and direct replay, in that order. Host load was
recorded, without sample filtering or an idleness test.

All 36 scheduled captures completed. Each contains one callback invocation,
passes event-origin and per-bucket attribution checks, and returns the same
nonempty result hash as its ordinary native invocation. All three repetitions
at each operation/degree give identical request counts and byte totals. The
raw DHAT event files are stored losslessly with deterministic gzip compression,
alongside logs, metadata, counters and exact collector sources. The regression
suite checks all observations, including their raw hashes and native answers.

Requested bytes per callback, including both roots where applicable:

| Degree | Operation | `lean_alloc_*` | Direct mimalloc | GMP | Sum |
| --- | --- | ---: | ---: | ---: | ---: |
| 3 | Completion | 654,840 | 69,200 | 785,216 | 1,509,256 |
| 3 | Comparison | 6,283,680 | 624,384 | 10,490,208 | 17,398,272 |
| 3 | Reduced replay | 1,672,112 | 130,416 | 2,584,336 | 4,386,864 |
| 3 | Direct replay | 1,627,520 | 132,480 | 2,792,784 | 4,552,784 |
| 7 | Completion | 2,456,488 | 262,768 | 4,638,944 | 7,358,200 |
| 7 | Comparison | 28,727,824 | 2,477,744 | 73,533,776 | 104,739,344 |
| 7 | Reduced replay | 7,514,784 | 501,840 | 17,581,744 | 25,598,368 |
| 7 | Direct replay | 8,170,552 | 513,056 | 20,952,960 | 29,636,568 |
| 15 | Completion | 10,214,792 | 957,504 | 26,977,232 | 38,149,528 |
| 15 | Comparison | 156,107,456 | 9,541,312 | 514,401,904 | 680,050,672 |
| 15 | Reduced replay | 39,626,656 | 1,917,200 | 118,130,992 | 159,674,848 |
| 15 | Direct replay | 49,448,112 | 1,958,800 | 155,862,408 | 207,269,320 |

GMP accounts for approximately 60.3% of comparison's intercepted bytes at
degree 3 and 75.6% at degree 15. Both degree and derivative coefficient sizes
grow in this family; these observations do not isolate a coefficient-height
effect or establish an asymptotic allocation law. Completion and comparison
also construct and check different numbers of tables, as specified in the
running-time report. The sums describe these complete current callbacks.

The direct-call audit finds only the wrapped `mi_malloc` and `mi_new_n`
allocation paths, plus freeing and allocator setup calls, outside mimalloc
internals. This is not proof of coverage of indirect/inlined alternatives,
arbitrary foreign allocators or allocations in spawned threads. These are
pure single-threaded benchmark callbacks; no general-purpose allocation API
or total-process/live-heap claim follows. DHAT records the same requests as
the counters, so their agreement verifies attribution, not independent allocator
coverage. Instrumented elapsed times and RSS are retained but include Valgrind
and preparation overhead and are not used as timing or live-memory evidence.

Reproduce with the committed driver and installed Valgrind headers:

```sh
python3 scripts/bench/sign_det_allocations.py \
  --functions Hex.SignDetBench.Joint.runCompletion Hex.SignDetBench.Joint.runComparison \
              Hex.SignDetBench.Joint.runCheckReduced Hex.SignDetBench.Joint.runCheckDirect \
  --parameters 3 7 15 --trials 3 \
  --valgrind /path/to/valgrind --include /path/to/valgrind/include \
  --output /path/to/new-capture-directory
```

The original capture directory is retained at
`/home/kim/.local/state/hex/issue-10377-profiles/allocation-joint-scaling-25b179f5c`.
No completed observation is discarded. This collection supplies allocation
observations for joint completion, comparison and replay. Maximal support,
independent coefficient-height and nested-field families, live memory, and the
remaining Phase-4 obligations require their own evidence. It does not resolve
the running-time report's inconclusive verdicts or complete #10377.
