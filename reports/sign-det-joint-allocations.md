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
result hash as its ordinary native invocation. Replay must return `true` (hash
`0xb`); a consistently false result is rejected by the retained-record check.
Completion and comparison hashes also match the independently validated
[ordinary benchmark answers](data/sign-det-joint-timing/394c3c548/metadata.json)
for each degree. Agreement with a native invocation alone would not establish
that the operation succeeded or answered correctly. All three repetitions
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

The [table-production records](data/sign-det-allocations/joint-production-25b179f5c/metadata.json)
add 18 captures: reduced and direct joint table production at the same three
degrees, in three fixed trial-major rounds on CPU 46 of the same host. They use
the identical executable, generated callback and collector sources. Their
answers match the independently validated ordinary production records, and all
three repetitions agree exactly. Requested bytes per production callback:

| Degree | Operation | `lean_alloc_*` | Direct mimalloc | GMP | Sum |
| --- | --- | ---: | ---: | ---: | ---: |
| 3 | Reduced production | 2,892,224 | 307,360 | 4,875,552 | 8,075,136 |
| 3 | Direct production | 2,929,288 | 317,056 | 5,572,448 | 8,818,792 |
| 7 | Reduced production | 12,797,392 | 1,197,120 | 33,464,032 | 47,458,544 |
| 7 | Direct production | 14,744,040 | 1,249,008 | 41,929,696 | 57,922,744 |
| 15 | Reduced production | 68,578,368 | 4,555,792 | 232,166,688 | 305,300,848 |
| 15 | Direct production | 91,489,984 | 4,780,880 | 318,135,480 | 414,406,344 |

A separate [degree-31 comparison capture](data/sign-det-allocations/comparison-31-25b179f5c/metadata.json)
on CPU 59 intercepts 386,473,472 GMP requests, requesting 3,784,472,776 bytes.
Lean entry points contribute 1,012,179,032 bytes and direct mimalloc entry points
37,090,608 bytes, giving 4,833,742,416 intercepted bytes. The answer matches the
ordinary degree-31 benchmark. This single observation is a cross-tool check,
not a scaling estimate. The earlier heaptrack capture attributed a lower bound
of 385,922,080 GMP requests to that callback; the present count exceeds that
bound. Within its substring-filtered stacks, heaptrack also gives an upper
bound of 386,079,828 calls, 393,644 below the new count. That is not an upper
bound for the whole callback: unwinding can omit the matched helper as well
as the callback frame. The binaries differ. Their `bench/HexSignDet/Joint.lean`
is identical, but replay cache-binding checks, root-list and selected-sign
implementation modules differ. The cross-tool comparison is therefore
inconclusive across revisions and establishes no coverage guarantee. Each supplementary collection retains its own three controlled
ABI fixtures, logs, metadata and losslessly compressed raw events.

The direct-call audit records direct calls to symbols whose names start with
`mi_`, from callers whose names do not start with `mi_` or `_mi_`. It records
`mi_malloc` and `mi_new_n`, plus freeing and allocator setup calls. It does
not inspect calls to `_mi_*`, libc allocation functions or `operator new`.
It does not prove coverage of indirect/inlined alternatives,
arbitrary foreign allocators or allocations in spawned threads. These are
pure single-threaded benchmark callbacks; no general-purpose allocation API
or total-process/live-heap claim follows. DHAT records the same requests as
the counters, so their agreement verifies attribution, not independent allocator
coverage. Instrumented elapsed times and RSS are retained but include Valgrind
and preparation overhead and are not used as timing or live-memory evidence.

Reproduce with the committed driver and installed Valgrind headers. The driver
checks instrumented/native answer agreement only. These retained answers are
checked afterward by the regression suite against the independently validated
ordinary benchmark answers; a newly collected dataset also needs an independent
answer check before interpreting it as a successful computation:

```sh
python3 scripts/bench/sign_det_allocations.py \
  --functions Hex.SignDetBench.Joint.runCompletion Hex.SignDetBench.Joint.runComparison \
              Hex.SignDetBench.Joint.runCheckReduced Hex.SignDetBench.Joint.runCheckDirect \
  --parameters 3 7 15 --trials 3 \
  --valgrind /path/to/valgrind --include /path/to/valgrind/include \
  --output /path/to/new-capture-directory
```

The original capture directories are retained under
`/home/kim/.local/state/hex/issue-10377-profiles/` as
`allocation-joint-scaling-25b179f5c`, `allocation-joint-production-25b179f5c`
and `allocation-comparison-31-25b179f5c`. To reproduce the supplementary
schedules, use the same command with `runReduced runDirect` and degrees
`3 7 15` in three trials, or `runComparison` with degree `31` in one trial.
The [source reconstruction](data/sign-det-allocations/joint-25b179f5c/source-reconstruction.json)
retains a patch against reachable main ancestor `e9711a9f7a405d7d00b0a5a974af7f41eda990cd`;
the regression suite reconstructs every measured source and checks its recorded
hash without depending on the continued existence of the branch commit.
A separate [post-capture inspection](data/sign-det-allocations/joint-25b179f5c/post-capture-build-identity.json)
records the executable and owned build-cache realpaths, device/inode identity
and unchanged executable hash. It is a later observation, not a retroactive
start-of-run check. The project build directory belongs to the measured
`hex-dev-issue-10377-allocation` worktree; package caches can be shared. Before/after binary hashes bind the
captured executable itself. Retained disassembly confirms that both
`lean::alloc_mpz` and `lean_alloc_mpz` call the wrapped
`lean_alloc_small_object_core` in this binary. This resolves that specific
possible bypass, without certifying every inlined or indirect path.

The generated joint benchmark C source is also retained losslessly; its hash
matches the generated source identified by every capture.

No completed observation is discarded. All 55 scheduled observations completed.
This collection supplies allocation observations for joint table production,
completion, comparison and replay. A separate
[complete matrix collection](sign-det-matrix-allocations.md) measures the finite
maximal-support solver and checker. Complete polynomial-query families, independent
coefficient-height and nested-field families, live memory and the remaining
Phase-4 obligations require their own evidence. It does not resolve
the running-time report's inconclusive verdicts or complete #10377.
